type stream = {
  mutable line_num : int;
  mutable chr : char list;
  chan : in_channel;
}

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  (* Functions *)
  | Primitive of string * (lobject list -> lobject)

exception SyntaxError of string
exception ThisCan'tHappenError
exception NotFound of string
exception TypeError of string

let read_char stm =
  match stm.chr with
  | [] ->
      let c = input_char stm.chan in
      if c = '\n' then
        let _ = stm.line_num <- stm.line_num + 1 in
        c
      else c
  | c :: rest ->
      let _ = stm.chr <- rest in
      c

let unread_char stm c = stm.chr <- c :: stm.chr
let is_white c = c = ' ' || c = '\t' || c = '\n'

let rec eat_whitespace stm =
  let c = read_char stm in
  if is_white c then eat_whitespace stm else unread_char stm c;
  ()

let string_of_char c = String.make 1 c

let rec read_sexp stm =
  let is_digit c =
    let code = Char.code c in
    code >= Char.code '0' && code <= Char.code '9'
  in
  let rec read_fixnum acc =
    let nc = read_char stm in
    if is_digit nc then read_fixnum (acc ^ Char.escaped nc)
    else
      let _ = unread_char stm nc in
      Fixnum (int_of_string acc)
  in
  let start_char_is_sym =
    let is_alpha = function 'A' .. 'Z' | 'a' .. 'z' -> true | _ -> false in
    function
    (* These characters always denote the start of a symbol *)
    | '*' | '/' | '>' | '<' | '=' | '?' | '!' | '-' | '+' -> true
    | c -> is_alpha c
  in
  let rec read_symbol () =
    let literal_quote = String.get "\"" 0 in
    let is_delimiter = function
      | '(' | ')' | '{' | '}' | ';' -> true
      | c when c = literal_quote -> true
      | c -> is_white c
    in
    let nc = read_char stm in
    if is_delimiter nc then
      (* If we encounter a delimiter, we unread the char
         and return an empty string *)
      let _ = unread_char stm nc in
      ""
    else string_of_char nc ^ read_symbol ()
  in
  let rec read_list stm =
    eat_whitespace stm;
    let c = read_char stm in
    if c = ')' then Nil
    else
      let _ = unread_char stm c in
      let car = read_sexp stm in
      let cdr = read_list stm in
      Pair (car, cdr)
  in
  eat_whitespace stm;
  let c = read_char stm in
  if start_char_is_sym c then Symbol (string_of_char c ^ read_symbol ())
  else if is_digit c || c = '~' then
    read_fixnum (string_of_char (if c = '~' then '-' else c))
  else if c = '(' then read_list stm
  else if c = '#' then
    match read_char stm with
    | 't' -> Boolean true
    | 'f' -> Boolean false
    | x -> raise (SyntaxError ("Invalid boolean literal " ^ Char.escaped x))
  else raise (SyntaxError ("Unexpected char " ^ Char.escaped c))

let rec is_list e =
  match e with Nil -> true | Pair (_, b) -> is_list b | _ -> false

let rec print_sexp e =
  let rec print_list l =
    match l with
    | Pair (a, Nil) -> print_sexp a
    | Pair (a, b) ->
        print_sexp a;
        print_string " ";
        print_list b
    | _ -> raise ThisCan'tHappenError
  in
  let print_pair p =
    match p with
    | Pair (a, b) ->
        print_sexp a;
        print_string " . ";
        print_sexp b
    | _ -> raise ThisCan'tHappenError
  in
  match e with
  | Fixnum v -> print_int v
  | Boolean b -> print_string (if b then "#t" else "#f")
  | Symbol s -> print_string s
  | Nil -> print_string "nil"
  | Pair (_, _) ->
      print_string "(";
      if is_list e then print_list e else print_pair e;
      print_string ")"
  | Primitive (name, _) -> print_string ("#<primitive:" ^ name ^ ">")

(* Params: Symbol, Environment *)
let rec lookup (n, e) =
  match e with
  | Nil -> raise (NotFound n)
  | Pair (Pair (Symbol n', v), rst) -> if n = n' then v else lookup (n, rst)
  | _ -> raise ThisCan'tHappenError

(* Params: Symbol, Value, Environment *)
let bind (n, v, e) = Pair (Pair (Symbol n, v), e)

let rec pair_to_list pr =
  match pr with
  | Nil -> []
  | Pair (a, b) -> a :: pair_to_list b
  | _ -> raise ThisCan'tHappenError

let basis =
  let prim_plus = function
    | [ Fixnum a; Fixnum b ] -> Fixnum (a + b)
    | _ -> raise (TypeError "(+ int int)")
  in
  let prim_pair = function
    | [ a; b ] -> Pair (a, b)
    | _ -> raise (TypeError "(pair a b)")
  in
  let new_prim acc (name, func) = bind (name, Primitive (name, func), acc) in
  List.fold_left new_prim Nil [ ("+", prim_plus); ("pair", prim_pair) ]

let rec eval_sexp sexp env =
  let eval_if cond if_true if_false =
    let cond_val, _ = eval_sexp cond env in
    match cond_val with
    | Boolean true -> if_true
    | Boolean false -> if_false
    | _ -> raise (TypeError "(if bool e1 e2)")
  in
  match sexp with
  | Fixnum v -> (Fixnum v, env)
  | Boolean v -> (Boolean v, env)
  | Symbol name -> (lookup (name, env), env)
  | Nil -> (Nil, env)
  | Primitive (n, f) -> (Primitive (n, f), env)
  | Pair (_, _) when is_list sexp -> (
      match pair_to_list sexp with
      | [ Symbol "if"; cond; if_true; if_false ] ->
          (fst (eval_sexp (eval_if cond if_true if_false) env), env)
      | [ Symbol "env" ] -> (env, env)
      | [ Symbol "pair"; car; cdr ] -> (Pair (car, cdr), env)
      | [ Symbol "val"; Symbol name; exp ] ->
          let exp_val, _ = eval_sexp exp env in
          let env' = bind (name, exp_val, env) in
          (exp_val, env')
      | Symbol fn :: args -> (
          let eval_curr_env exp = fst (eval_sexp exp env) in
          let evaluated_args = List.map eval_curr_env args in
          match eval_sexp (Symbol fn) env with
          | Primitive (n, f), _ -> (f evaluated_args, env)
          | _ -> raise (TypeError "(apply func args)"))
      | _ -> (sexp, env))
  (* Leave pairs as they are for now *)
  | _ -> (sexp, env)

let rec repl stm env =
  print_string "> ";
  flush stdout;
  let sexp = read_sexp stm in
  let result, env' = eval_sexp sexp env in
  print_sexp result;
  print_newline ();
  repl stm env'

let main =
  let stm = { chr = []; line_num = 1; chan = stdin } in
  repl stm basis

let () = main
