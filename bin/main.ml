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

exception SyntaxError of string
exception ThisCan'tHappenError

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

let rec print_sexp e =
  let rec is_list e =
    match e with Nil -> true | Pair (_, b) -> is_list b | _ -> false
  in
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
        print_string " ";
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

let rec repl stm =
  print_string "> ";
  flush stdout;
  let sexp = read_sexp stm in
  print_sexp sexp;
  print_newline ();
  repl stm

let main =
  let stm = { chr = []; line_num = 1; chan = stdin } in
  repl stm

let () = main
