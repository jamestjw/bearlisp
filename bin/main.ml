type stream = {
  mutable line_num : int;
  mutable chr : char list;
  chan : in_channel;
}

(* Environment *)
type 'a env = (string * 'a option ref) list

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  (* Functions *)
  | Primitive of string * (lobject list -> lobject)
  | Quote of value
  | Closure of name list * exp * value env

and value = lobject
and name = string
and let_kind = LET | LETSTAR | LETREC

and exp =
  | Literal of value
  | Var of name
  | If of exp * exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Apply of exp * exp
  | Call of exp * exp list
  | Defexp of def
  | Lambda of name list * exp
  | Let of let_kind * (name * exp) list * exp

and def = Val of name * exp | Exp of exp | Def of name * name list * exp

exception SyntaxError of string
exception ThisCan'tHappenError
exception NotFound of string
exception TypeError of string
exception ParseError of string
exception UnspecifiedValue of string
exception UniqueError of string

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
  else if c = '\'' then Quote (read_sexp stm)
  else raise (SyntaxError ("Unexpected char " ^ Char.escaped c))

let rec is_list e =
  match e with Nil -> true | Pair (_, b) -> is_list b | _ -> false

(* Params: Symbol, Environment *)
let rec lookup = function
  | n, [] -> raise (NotFound n)
  | n, (n', v) :: _ when n = n' -> (
      match !v with Some v' -> v' | None -> raise (UnspecifiedValue n))
  | n, (_, _) :: bs -> lookup (n, bs)

(* Params: Symbol, Value, Environment *)
let bind (n, v, e) = (n, ref (Some v)) :: e
let mkloc _ = ref None

let bindloc : name * 'a option ref * 'a env -> 'a env =
 fun (n, vor, e) -> (n, vor) :: e

let bind_list ns vs env =
  List.fold_left2 (fun acc n v -> bind (n, v, acc)) env ns vs

let bindloc_list ns vs env =
  List.fold_left2 (fun acc n v -> bindloc (n, v, acc)) env ns vs

let rec env_to_val =
  let b_to_val (n, vor) =
    Pair (Symbol n, match !vor with None -> Symbol "unspecified" | Some v -> v)
  in
  function [] -> Nil | b :: bs -> Pair (b_to_val b, env_to_val bs)

let rec pair_to_list pr =
  match pr with
  | Nil -> []
  | Pair (a, b) -> a :: pair_to_list b
  | _ -> raise ThisCan'tHappenError

let basis =
  let prim_pair = function
    | [ a; b ] -> Pair (a, b)
    | _ -> raise (TypeError "(pair a b)")
  in
  let rec prim_list = function
    | [] -> Nil
    | car :: cdr -> Pair (car, prim_list cdr)
  in
  let prim_car = function
    | [ Pair (car, _) ] -> car
    | _ -> raise (TypeError "(car non-nil-pair)")
  in
  let prim_cdr = function
    | [ Pair (_, cdr) ] -> cdr
    | _ -> raise (TypeError "(cdr non-nil-pair)")
  in
  let prim_atomp = function
    | [ Pair (_, _) ] -> Boolean false
    | [ _ ] -> Boolean true
    | _ -> raise (TypeError "(atom? something)")
  in
  let prim_eq = function
    | [ a; b ] -> Boolean (a = b)
    | _ -> raise (TypeError "(eq a b)")
  in
  let prim_symp = function
    | [ Symbol _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise (TypeError "(sym? something)")
  in
  let num_prim name op =
    ( name,
      function
      | [ Fixnum a; Fixnum b ] -> Fixnum (op a b)
      | _ -> raise (TypeError ("(" ^ name ^ " int int)")) )
  in
  let cmp_prim name op =
    ( name,
      function
      | [ Fixnum a; Fixnum b ] -> Boolean (op a b)
      | _ -> raise (TypeError ("(" ^ name ^ " int int)")) )
  in
  let new_prim acc (name, func) = bind (name, Primitive (name, func), acc) in
  List.fold_left new_prim []
    [
      ("list", prim_list);
      ("pair", prim_pair);
      ("car", prim_car);
      ("cdr", prim_cdr);
      ("eq", prim_eq);
      ("atom?", prim_atomp);
      ("sym?", prim_symp);
      num_prim "+" ( + );
      num_prim "-" ( - );
      num_prim "*" ( * );
      num_prim "/" ( / );
      cmp_prim "<" ( < );
      cmp_prim ">" ( > );
      cmp_prim "=" ( = );
    ]

let extend new_env old_env =
  List.fold_right (fun (b, v) acc -> bindloc (b, v, acc)) new_env old_env

let rec eval_exp exp env =
  let eval_apply f args =
    match f with
    | Primitive (_, f) -> f args
    (* A closure is evaluated by first binding the arguments to the environment,
       and then executing the relevant expression using this environment *)
    | Closure (ns, exp, closure_env) ->
        eval_exp exp (bind_list ns args closure_env)
    | _ -> raise (TypeError "(apply prim '(args)) or (prim args)")
  in
  let rec unzip ls = (List.map fst ls, List.map snd ls) in
  let rec ev = function
    | Literal (Quote e) -> e
    | Literal l -> l
    | Var n -> lookup (n, env)
    | If (c, t, f) -> (
        match ev c with
        | Boolean true -> ev t
        | Boolean false -> ev f
        | _ -> raise (TypeError "(if bool e1 e2)"))
    | And (c1, c2) -> (
        match (ev c1, ev c2) with
        | Boolean v1, Boolean v2 -> Boolean (v1 && v2)
        | _ -> raise (TypeError "(and bool bool)"))
    | Or (c1, c2) -> (
        match (ev c1, ev c2) with
        | Boolean v1, Boolean v2 -> Boolean (v1 || v2)
        | _ -> raise (TypeError "(or bool bool)"))
    | Apply (fn, e) -> eval_apply (ev fn) (pair_to_list (ev e))
    | Call (Var "env", []) -> env_to_val env
    | Call (e, es) -> eval_apply (ev e) (List.map ev es)
    | Lambda (ns, e) -> Closure (ns, e, env)
    | Let (LET, bindings, body) ->
        let evbinding (n, e) = (n, ref (Some (ev e))) in
        eval_exp body (extend (List.map evbinding bindings) env)
    | Let (LETSTAR, bindings, body) ->
        let evbinding acc (n, e) = bind (n, eval_exp e acc, acc) in
        eval_exp body (extend (List.fold_left evbinding [] bindings) env)
    | Let (LETREC, bs, body) ->
        let names, values = unzip bs in
        let env' = bindloc_list names (List.map mkloc values) env in
        let updates = List.map (fun (n, e) -> (n, Some (eval_exp e env'))) bs in
        let () = List.iter (fun (n, v) -> List.assoc n env' := v) updates in
        eval_exp body env'
    | Defexp _ -> raise ThisCan'tHappenError
  in

  ev exp

let eval_def def env =
  match def with
  | Val (n, e) ->
      let v = eval_exp e env in
      (v, bind (n, v, env))
  | Exp e -> (eval_exp e env, env)
  | Def (n, ns, e) ->
      let formals, body, closure_env =
        match eval_exp (Lambda (ns, e)) env with
        | Closure (fs, body', env) -> (fs, body', env)
        | _ -> raise (TypeError "Expecting closure.")
      in
      let loc = mkloc () in
      let clo = Closure (formals, body, bindloc (n, loc, closure_env)) in
      (* So that the closure has a reference to itself *)
      let () = loc := Some clo in
      (clo, bindloc (n, loc, env))

let eval ast env =
  match ast with Defexp d -> eval_def d env | e -> (eval_exp e env, env)

let rec assert_unique = function
  | [] -> ()
  | x :: xs -> if List.mem x xs then raise (UniqueError x) else assert_unique xs

let rec build_ast sexp =
  let rec cond_to_if = function
    (* TODO: For now, the interpreter returns an error in the
       final else statement no matter what *)
    | [] -> Literal (Symbol "error")
    | Pair (cond, Pair (res, Nil)) :: cond_pairs ->
        If (build_ast cond, build_ast res, cond_to_if cond_pairs)
    | _ -> raise (TypeError "(cond conditions)")
  in
  let let_kinds = [ ("let", LET); ("let*", LETSTAR); ("letrec", LETREC) ] in
  let valid_let s = List.mem_assoc s let_kinds in
  let to_kind s = List.assoc s let_kinds in
  match sexp with
  | Primitive _ | Closure _ -> raise ThisCan'tHappenError
  | Fixnum _ | Boolean _ | Nil | Quote _ -> Literal sexp
  | Symbol s -> Var s
  | Pair _ when is_list sexp -> (
      match pair_to_list sexp with
      | [ Symbol "if"; cond; if_true; if_false ] ->
          If (build_ast cond, build_ast if_true, build_ast if_false)
      | [ Symbol "and"; c1; c2 ] -> And (build_ast c1, build_ast c2)
      | [ Symbol "or"; c1; c2 ] -> Or (build_ast c1, build_ast c2)
      | [ Symbol "val"; Symbol n; e ] -> Defexp (Val (n, build_ast e))
      | [ Symbol "apply"; fnexp; args ] ->
          Apply (build_ast fnexp, build_ast args)
      | [ Symbol "quote "; e ] -> Literal (Quote e)
      | [ Symbol "lambda"; ns; e ] when is_list ns ->
          let err () = raise (TypeError "(lambda (formals) body)") in
          let names =
            List.map (function Symbol s -> s | _ -> err ()) (pair_to_list ns)
          in
          Lambda (names, build_ast e)
      | [ Symbol "define"; Symbol n; ns; e ] ->
          let err () = raise (TypeError "(define name (formals) body)") in
          let names =
            List.map (function Symbol s -> s | _ -> err ()) (pair_to_list ns)
          in
          Defexp (Def (n, names, build_ast e))
      | Symbol "cond" :: conditions -> cond_to_if conditions
      | [ Symbol s; bindings; exp ] when is_list bindings && valid_let s ->
          let mkbinding = function
            | Pair (Symbol n, Pair (e, Nil)) -> (n, build_ast e)
            | _ -> raise (TypeError "(let bindings exp)")
          in
          let bindings = List.map mkbinding (pair_to_list bindings) in
          let () = assert_unique (List.map fst bindings) in
          Let (to_kind s, bindings, build_ast exp)
      | fnexp :: args -> Call (build_ast fnexp, List.map build_ast args)
      | [] -> raise (ParseError "poorly formed expression"))
  | Pair _ -> Literal sexp

let spacesep ns = String.concat " " ns

let rec string_exp =
  let spacesep_exp exps = spacesep (List.map string_exp exps) in
  let string_of_binding (n, e) = "(" ^ n ^ " " ^ string_exp e ^ ")" in
  function
  | Literal e -> string_val e
  | Var n -> n
  | If (c, t, f) ->
      "(if " ^ string_exp c ^ " " ^ string_exp t ^ " " ^ string_exp f ^ ")"
  | And (c1, c2) -> "(and " ^ string_exp c1 ^ " " ^ string_exp c2 ^ ")"
  | Or (c1, c2) -> "(or " ^ string_exp c1 ^ " " ^ string_exp c2 ^ ")"
  | Apply (f, e) -> "(apply " ^ string_exp f ^ " " ^ string_exp e ^ ")"
  | Call (f, exps) -> "(" ^ string_exp f ^ " " ^ spacesep_exp exps ^ ")"
  | Defexp (Val (n, e)) -> "(val " ^ n ^ " " ^ string_exp e ^ ")"
  | Defexp (Exp e) -> string_exp e
  | Defexp (Def (n, ns, e)) ->
      "(define " ^ n ^ "(" ^ spacesep ns ^ ") " ^ string_exp e ^ ")"
  | Lambda (ns, e) -> "(lambda (" ^ spacesep ns ^ ") " ^ string_exp e ^ ")"
  | Let (kind, bs, e) ->
      let str =
        match kind with LET -> "let" | LETSTAR -> "let*" | LETREC -> "letrec"
      in
      let bindings = spacesep (List.map string_of_binding bs) in
      "(" ^ str ^ " (" ^ bindings ^ ") " ^ string_exp e ^ ")"

and string_val e =
  let rec string_list l =
    match l with
    | Pair (a, Nil) -> string_val a
    | Pair (a, b) -> string_val a ^ " " ^ string_list b
    | _ -> raise ThisCan'tHappenError
  in
  let string_pair p =
    match p with
    | Pair (a, b) -> string_val a ^ " . " ^ string_val b
    | _ -> raise ThisCan'tHappenError
  in
  match e with
  | Fixnum v -> string_of_int v
  | Boolean b -> if b then "#t" else "#f"
  | Symbol s -> s
  | Nil -> "nil"
  | Pair (_, _) ->
      "(" ^ (if is_list e then string_list e else string_pair e) ^ ")"
  | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
  | Quote v -> "'" ^ string_val v
  | Closure _ -> "#<closure>"

let rec repl stm env =
  print_string "> ";
  flush stdout;
  let ast = build_ast (read_sexp stm) in
  let result, env' = eval ast env in
  let () = print_endline (string_val result) in
  repl stm env'

let main =
  let stm = { chr = []; line_num = 1; chan = stdin } in
  repl stm basis

let () = main
