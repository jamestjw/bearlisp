exception ThisCan'tHappenError
exception UniqueError of string
exception TypeError of string

let string_of_char c = String.make 1 c

let rec assert_unique = function
  | [] -> ()
  | x :: xs -> if List.mem x xs then raise (UniqueError x) else assert_unique xs

module Env : sig
  type 'a env = (string * 'a option ref) list

  exception UnspecifiedValue of string
  exception NotFound of string

  val mkloc : 'a -> 'b option ref
  val bind : string * 'a * 'a env -> 'a env
  val bindloc : string * 'a option ref * 'a env -> 'a env
  val bind_list : string list -> 'a list -> 'a env -> 'a env
  val bindloc_list : string list -> 'a option ref list -> 'a env -> 'a env
  val lookup : string * 'a env -> 'a
  val extend : 'a env -> 'a env -> 'a env
end = struct
  type 'a env = (string * 'a option ref) list

  exception UnspecifiedValue of string
  exception NotFound of string

  let bind (n, v, e) = (n, ref (Some v)) :: e
  let mkloc _ = ref None
  let bindloc (n, vor, e) = (n, vor) :: e

  let bind_list ns vs env =
    List.fold_left2 (fun acc n v -> bind (n, v, acc)) env ns vs

  let bindloc_list ns vs env =
    List.fold_left2 (fun acc n v -> bindloc (n, v, acc)) env ns vs

  (* Params: Symbol, Environment *)
  let rec lookup = function
    | n, [] -> raise (NotFound n)
    | n, (n', v) :: _ when n = n' -> (
        match !v with Some v' -> v' | None -> raise (UnspecifiedValue n))
    | n, (_, _) :: bs -> lookup (n, bs)

  let extend new_env old_env =
    List.fold_right (fun (b, v) acc -> bindloc (b, v, acc)) new_env old_env
end

module Ast = struct
  type lobject =
    | Fixnum of int
    | Boolean of bool
    | Symbol of string
    | Nil
    | Pair of lobject * lobject
    (* Functions *)
    | Primitive of string * (lobject list -> lobject)
    | Quote of value
    | Closure of name list * exp * value Env.env

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

  let rec string_exp =
    let spacesep ns = String.concat " " ns in
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
          match kind with
          | LET -> "let"
          | LETSTAR -> "let*"
          | LETREC -> "letrec"
        in
        let bindings = spacesep (List.map string_of_binding bs) in
        "(" ^ str ^ " (" ^ bindings ^ ") " ^ string_exp e ^ ")"

  and string_val e =
    match e with
    | Fixnum v -> string_of_int v
    | Boolean b -> if b then "#t" else "#f"
    | Symbol s -> s
    | Nil -> "nil"
    | Pair (car, cdr) ->
        let rec tail_string_val = function
          | Pair (car', cdr') -> " " ^ string_val car' ^ tail_string_val cdr'
          | Nil -> ")"
          | v -> " . " ^ string_val v ^ ")"
        in
        "(" ^ string_val car ^ tail_string_val cdr
    | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
    | Quote v -> "'" ^ string_val v
    | Closure _ -> "#<closure>"

  let rec pair_to_list pr =
    match pr with
    | Nil -> []
    | Pair (a, b) -> a :: pair_to_list b
    | _ -> raise ThisCan'tHappenError
end

module PushbackReader : sig
  type 'a t

  val of_string : string -> char t
  val of_channel : in_channel -> char t
  val read_char : char t -> char
  val unread_char : char t -> char -> char t
  val do_stdin : 'a t -> 'b -> ('b -> unit) -> unit
end = struct
  type 'a t = {
    mutable line_num : int;
    mutable chr : char list;
    stdin : bool;
    stm : 'a Stream.t;
  }

  let make is_stdin stm = { chr = []; line_num = 1; stdin = is_stdin; stm }
  let of_string s = make false @@ Stream.of_string s
  let of_channel f = make (f = stdin) @@ Stream.of_channel f
  let do_stdin stm arg f = if stm.stdin then f arg else ()

  let read_char stm =
    match stm.chr with
    | [] ->
        let c = Stream.next stm.stm in
        if c = '\n' then (
          stm.line_num <- stm.line_num + 1;
          c)
        else c
    | c :: rest ->
        let _ = stm.chr <- rest in
        c

  let unread_char stm c =
    let () = stm.chr <- c :: stm.chr in
    stm
end

module type READER = sig
  val read_exp : char PushbackReader.t -> Ast.exp
end

module type EVALUATOR = sig
  val eval : Ast.exp -> Ast.value Env.env -> Ast.value * Ast.value Env.env
end

module Reader : READER = struct
  exception SyntaxError of string
  exception ParseError of string

  let is_white c = c = ' ' || c = '\t' || c = '\n'

  let rec eat_whitespace stm =
    let c = PushbackReader.read_char stm in
    if is_white c then eat_whitespace stm
    else
      let _ = PushbackReader.unread_char stm c in
      ()

  let rec read_sexp stm =
    let open Ast in
    let is_digit c =
      let code = Char.code c in
      code >= Char.code '0' && code <= Char.code '9'
    in
    let rec read_fixnum acc =
      let nc = PushbackReader.read_char stm in
      if is_digit nc then read_fixnum (acc ^ Char.escaped nc)
      else
        let _ = PushbackReader.unread_char stm nc in
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
      let nc = PushbackReader.read_char stm in
      if is_delimiter nc then
        (* If we encounter a delimiter, we unread the char
           and return an empty string *)
        let _ = PushbackReader.unread_char stm nc in
        ""
      else string_of_char nc ^ read_symbol ()
    in
    let rec read_list stm =
      eat_whitespace stm;
      let c = PushbackReader.read_char stm in
      if c = ')' then Nil
      else
        let _ = PushbackReader.unread_char stm c in
        let car = read_sexp stm in
        let cdr = read_list stm in
        Pair (car, cdr)
    in
    let rec eat_comment stm =
      if PushbackReader.read_char stm = '\n' then () else eat_comment stm
    in
    eat_whitespace stm;
    let c = PushbackReader.read_char stm in
    (* When we encounter a comment, consume characters until
       we encounter a newline *)
    if c = ';' then (
      eat_comment stm;
      read_sexp stm)
    else if start_char_is_sym c then Symbol (string_of_char c ^ read_symbol ())
    else if is_digit c || c = '~' then
      read_fixnum (string_of_char (if c = '~' then '-' else c))
    else if c = '(' then read_list stm
    else if c = '#' then
      match PushbackReader.read_char stm with
      | 't' -> Boolean true
      | 'f' -> Boolean false
      | x -> raise (SyntaxError ("Invalid boolean literal " ^ string_of_char x))
    else if c = '\'' then Quote (read_sexp stm)
    else raise (SyntaxError ("Unexpected char " ^ string_of_char c))

  let rec build sexp =
    let open Ast in
    let rec is_list e =
      match e with Nil -> true | Pair (_, b) -> is_list b | _ -> false
    in
    let rec cond_to_if = function
      (* TODO: For now, the interpreter returns an error in the
         final else statement no matter what *)
      | [] -> Literal (Symbol "error")
      | Pair (cond, Pair (res, Nil)) :: cond_pairs ->
          If (build cond, build res, cond_to_if cond_pairs)
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
            If (build cond, build if_true, build if_false)
        | [ Symbol "and"; c1; c2 ] -> And (build c1, build c2)
        | [ Symbol "or"; c1; c2 ] -> Or (build c1, build c2)
        | [ Symbol "val"; Symbol n; e ] -> Defexp (Val (n, build e))
        | [ Symbol "apply"; fnexp; args ] -> Apply (build fnexp, build args)
        | [ Symbol "quote "; e ] -> Literal (Quote e)
        | [ Symbol "lambda"; ns; e ] when is_list ns ->
            let err () = raise (TypeError "(lambda (formals) body)") in
            let names =
              List.map
                (function Symbol s -> s | _ -> err ())
                (pair_to_list ns)
            in
            Lambda (names, build e)
        | [ Symbol "define"; Symbol n; ns; e ] ->
            let err () = raise (TypeError "(define name (formals) body)") in
            let names =
              List.map
                (function Symbol s -> s | _ -> err ())
                (pair_to_list ns)
            in
            Defexp (Def (n, names, build e))
        | Symbol "cond" :: conditions -> cond_to_if conditions
        | [ Symbol s; bindings; exp ] when is_list bindings && valid_let s ->
            let mkbinding = function
              | Pair (Symbol n, Pair (e, Nil)) -> (n, build e)
              | _ -> raise (TypeError "(let bindings exp)")
            in
            let bindings = List.map mkbinding (pair_to_list bindings) in
            let () = assert_unique (List.map fst bindings) in
            Let (to_kind s, bindings, build exp)
        | fnexp :: args -> Call (build fnexp, List.map build args)
        | [] -> raise (ParseError "poorly formed expression"))
    | Pair _ -> Literal sexp

  let read_exp stm = build @@ read_sexp stm
end

module Evaluator : EVALUATOR = struct
  open Ast

  let rec env_to_val =
    let b_to_val (n, vor) =
      Pair
        (Symbol n, match !vor with None -> Symbol "unspecified" | Some v -> v)
    in
    function [] -> Nil | b :: bs -> Pair (b_to_val b, env_to_val bs)

  let rec eval_exp exp env =
    let eval_apply f args =
      match f with
      | Primitive (_, f) -> f args
      (* A closure is evaluated by first binding the arguments to the environment,
         and then executing the relevant expression using this environment *)
      | Closure (ns, exp, closure_env) ->
          eval_exp exp (Env.bind_list ns args closure_env)
      | _ -> raise (TypeError "(apply prim '(args)) or (prim args)")
    in
    let rec unzip ls = (List.map fst ls, List.map snd ls) in
    let rec ev = function
      | Literal (Quote e) -> e
      | Literal l -> l
      | Var n -> Env.lookup (n, env)
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
          eval_exp body (Env.extend (List.map evbinding bindings) env)
      | Let (LETSTAR, bindings, body) ->
          let evbinding acc (n, e) = Env.bind (n, eval_exp e acc, acc) in
          eval_exp body (List.fold_left evbinding env bindings)
      | Let (LETREC, bs, body) ->
          let names, values = unzip bs in
          let env' = Env.bindloc_list names (List.map Env.mkloc values) env in
          let updates =
            List.map (fun (n, e) -> (n, Some (eval_exp e env'))) bs
          in
          let () = List.iter (fun (n, v) -> List.assoc n env' := v) updates in
          eval_exp body env'
      | Defexp _ -> raise ThisCan'tHappenError
    in

    try ev exp
    with e ->
      let err = Printexc.to_string e in
      print_endline @@ "Error: '" ^ err ^ "' in expression " ^ string_exp exp;
      raise e

  let eval_def def env =
    match def with
    | Val (n, e) ->
        let v = eval_exp e env in
        (v, Env.bind (n, v, env))
    | Exp e -> (eval_exp e env, env)
    | Def (n, ns, e) ->
        let formals, body, closure_env =
          match eval_exp (Lambda (ns, e)) env with
          | Closure (fs, body', env) -> (fs, body', env)
          | _ -> raise (TypeError "Expecting closure.")
        in
        let loc = Env.mkloc () in
        let clo = Closure (formals, body, Env.bindloc (n, loc, closure_env)) in
        (* So that the closure has a reference to itself *)
        let () = loc := Some clo in
        (clo, Env.bindloc (n, loc, env))

  let eval ast env =
    match ast with Defexp d -> eval_def d env | e -> (eval_exp e env, env)
end

let rec repl stm env =
  (* Print prompt if user is using the REPL via stdin *)
  PushbackReader.do_stdin stm "> " print_string;
  PushbackReader.do_stdin stm stdout flush;

  let ast = Reader.read_exp stm in
  let result, env' = Evaluator.eval ast env in
  (* Only print results if user is in REPL mode *)
  PushbackReader.do_stdin stm (Ast.string_val result) print_endline;
  repl stm env'

let get_input_channel () =
  try open_in Sys.argv.(1) with Invalid_argument _ -> stdin

exception MismatchError of string

let basis =
  let open Ast in
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
    | _ -> raise (TypeError "(sym? single-arg)")
  in
  let prim_getchar = function
    | [] -> (
        try Fixnum (int_of_char (input_char stdin))
        with End_of_file -> Fixnum (-1))
    | _ -> raise (TypeError "(getchar)")
  in
  let prim_print = function
    | [ v ] ->
        let () = print_string (string_val v) in
        Symbol "ok"
    | _ -> raise (TypeError "(print val)")
  in
  let prim_itoc = function
    | [ Fixnum i ] -> Symbol (string_of_char @@ char_of_int i)
    | _ -> raise (TypeError "(itoc int)")
  in
  let prim_cat = function
    | [ Symbol a; Symbol b ] -> Symbol (a ^ b)
    | _ -> raise (TypeError "(cat sym1 sym2)")
  in
  let num_prim name op =
    ( name,
      function
      | [ Fixnum a; Fixnum b ] -> Fixnum (op a b)
      | _ -> raise (MismatchError ("(" ^ name ^ " int int)")) )
  in
  let cmp_prim name op =
    ( name,
      function
      | [ Fixnum a; Fixnum b ] -> Boolean (op a b)
      | _ -> raise (MismatchError ("(" ^ name ^ " int int)")) )
  in
  let new_prim acc (name, func) =
    Env.bind (name, Primitive (name, func), acc)
  in
  List.fold_left new_prim
    [ ("empty-symbol", ref (Some (Symbol ""))) ]
    [
      ("list", prim_list);
      ("pair", prim_pair);
      ("car", prim_car);
      ("cdr", prim_cdr);
      ("eq", prim_eq);
      ("atom?", prim_atomp);
      ("sym?", prim_symp);
      ("getchar", prim_getchar);
      ("print", prim_print);
      ("itoc", prim_itoc);
      ("cat", prim_cat);
      num_prim "+" ( + );
      num_prim "-" ( - );
      num_prim "*" ( * );
      num_prim "/" ( / );
      cmp_prim "<" ( < );
      cmp_prim ">" ( > );
      cmp_prim "=" ( = );
    ]

let stdlib =
  let open Ast in
  let ev env e =
    match e with
    | Defexp _ -> Evaluator.eval e env
    | _ -> raise (TypeError "Can only have definitions in stdlib")
  in
  let rec slurp stm env =
    try stm |> Reader.read_exp |> ev env |> snd |> slurp stm
    with Stream.Failure -> env
  in
  let stm =
    PushbackReader.of_string
      "\n\
      \  (define o (f g) (lambda (x) (f (g x))))\n\
       (val caar (o car car))\n\
       (val cadr (o car cdr))\n\
       (val caddr (o cadr cdr))\n\
       (val cadar (o car (o cdr car)))\n\
       (val caddar (o car (o cdr (o cdr car))))\n\n\
       (val cons pair)\n\n\
       (val newline (itoc 10))\n\
       (val space (itoc 32))\n\n\
       ; This is pretty awkward looking because we have no other way to sequence\n\
       ; operations. We have no begin, nothing.\n\
       (define println (s)\n\
      \  (let ((ok (print s)))\n\
      \    (print newline)))\n\n\
       ; This is less awkward because we actually use ic and c.\n\
       (define getline ()\n\
      \  (let* ((ic (getchar))\n\
      \         (c (itoc ic)))\n\
      \    (if (or (eq c newline) (eq ic ~1))\n\
      \      empty-symbol\n\
      \      (cat c (getline)))))\n\n\
       (define null? (xs)\n\
      \  (eq xs '()))\n\n\
       (define length (ls)\n\
      \  (if (null? ls)\n\
      \    0\n\
      \    (+ 1 (length (cdr ls)))))\n\n\
       (define take (n ls)\n\
      \  (if (or (< n 1) (null? ls))\n\
      \    '()\n\
      \    (cons (car ls) (take (- n 1) (cdr ls)))))\n\n\
       (define drop (n ls)\n\
      \  (if (or (< n 1) (null? ls))\n\
      \    ls\n\
      \    (drop (- n 1) (cdr ls))))\n\n\
       (define merge (xs ys)\n\
      \  (if (null? xs)\n\
      \    ys\n\
      \    (if (null? ys)\n\
      \      xs\n\
      \      (if (< (car xs) (car ys))\n\
      \        (cons (car xs) (merge (cdr xs) ys))\n\
      \        (cons (car ys) (merge xs (cdr ys)))))))\n\n\
       (define mergesort (ls)\n\
      \  (if (null? ls)\n\
      \    ls\n\
      \    (if (null? (cdr ls))\n\
      \      ls\n\
      \      (let* ((size (length ls))\n\
      \             (half (/ size 2))\n\
      \             (first (take half ls))\n\
      \             (second (drop half ls)))\n\
      \        (merge (mergesort first) (mergesort second))))))\n\
      \  "
  in
  slurp stm basis

let main =
  let input_channel = get_input_channel () in
  try repl (PushbackReader.of_channel input_channel) stdlib
  with Stream.Failure -> if input_channel <> stdin then close_in input_channel

let () = main
