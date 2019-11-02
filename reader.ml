(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
 open PC;;
 
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 
 (* let read_sexpr string = raise X_not_yet_implemented ;;
 
 let read_sexprs string = raise X_not_yet_implemented;;
 
 end;;  *)
 (* struct Reader*)
 
 let rec power number pow = 
   match pow with
   0 -> number
   |_ -> if (pow>0) then (power (number*.10.) (pow-1)) else (power (number/.10.) (pow+1));; 
 
 let whitespaces = star nt_whitespace;;
 
 let make_enclosed l p r =
   let enclosed = caten (caten l p) r in
   pack enclosed (fun ((left, pi), right) -> pi);;
 
 let make_spaced p = make_enclosed whitespaces p whitespaces;;
 
 let lbar = make_spaced (char '[');;
 
 let rbar = make_spaced (char ']');;
 
 let lparen = make_spaced (char '(');;
 
 let rparen = make_spaced (char ')');;
 
 let dot = pack (char '.') (fun _ -> ".");;
 
 let hex_pre = pack (char_ci 'x') (fun _ -> true);;
 
 let number_hex_pre = pack (word_ci "#x") (fun _ -> true);;
 
 (* used for all parsers for taking care of the rest *)
 let rest nt = not_followed_by nt;;
 
 let digit = range '0' '9';;
 
 let symbol_char = 
   let low_letters = range 'a' 'z' in
   let upper_letters = range 'A' 'Z' in
   let special_symbols = one_of "!$^*-_=+<>?/:" in
   disj_list [digit; low_letters; upper_letters; special_symbols];;
 
 let hex_digit= 
   let low_letters = range 'a' 'f' in
   let upper_letters = range 'A' 'F' in
   disj_list [digit; low_letters; upper_letters];;
 
 let sign =
   let plus_sign = pack (char '+') (fun _ -> 1) in (* change to sexp Number *)
   let minum_sign = pack (char '-') (fun _ -> -1) in(* change to sexp Number *)
   disj plus_sign minum_sign;;
 
        (* --------------------------------------Symbol-------------------------------------- *)
 let nt_symbol = 
   let s_char = pack symbol_char (fun ch -> lowercase_ascii ch) in
   let x = plus s_char in
   let symbol_caster = pack x (fun s -> Symbol(list_to_string s)) in
     (rest symbol_caster (word "#"));;
 
         (* --------------------------------------Boolean-------------------------------------- *)
 let nt_bool =
   let t = pack (word_ci "#t") (fun _ -> Bool true) in
   let f = pack (word_ci "#f") (fun _ -> Bool false) in
   (rest (disj t f) nt_symbol);;  
         (* --------------------------------------Number-------------------------------------- *)
 let nt_natural=
   let digits = plus digit in
   pack digits (fun (ds) -> (int_of_string(list_to_string ds)));;
 
 let nt_natural_for_float=
   let digits = plus digit in
   pack digits (fun (ds) -> (list_to_string ds));;
 
 let nt_number_dot = caten dot nt_natural_for_float;;
 
 let nt_integer= 
   let x = maybe sign in
   let x = pack x (function 
                 |None -> 1
                 |(Some mult)-> mult) in
   let y = nt_natural in
   let x = caten x y in
   let x = pack x 
   (function (mult, n) -> if (n = 0 && mult = -1) then "-0" else (string_of_int (mult * n))) in
   x;;
 
 let nt_float =
   let i = nt_integer in
   let d = nt_number_dot in
   let x = caten i d in
     pack x (function (integer,(dott,s))->
     (float_of_string(String.concat "." [integer; s])));;
 
 let nt_decimal_number=
   let integer_caster = pack nt_integer (fun x -> Number(Int (int_of_string x))) in
   let float_caster = pack nt_float (fun y -> Number(Float(y))) in
   disj float_caster integer_caster;;
 
 let nt_decimal_number_with_extention = 
   let integer_num = caten (caten nt_integer (char_ci 'e')) nt_integer in
   let float_num = caten (caten nt_float (char_ci 'e')) nt_integer in
   let x = pack integer_num (fun ((number, e), pow) -> Number(Float (power (float  (int_of_string number)) (int_of_string pow)))) in
   let y = pack float_num (fun ((number, e), pow) -> Number(Float (power number (int_of_string pow)))) in
   disj x y;;
 
 let nt_hex_natural=
   let hex_digits = plus hex_digit in
   pack hex_digits (fun (ds) -> int_of_string (String.concat "" ["0x" ; (list_to_string ds)]));;
 
 let nt_hex_float_natural=
   let hex_digits = plus hex_digit in
   pack hex_digits (fun (ds) -> float_of_string (String.concat "" ["0x0." ; (list_to_string ds)]));;
   
 let nt_hex_integer= 
   let x = maybe sign in
   let x = pack x (function 
                   |None -> 1
                   |(Some mult)-> mult) in
   let y = nt_hex_natural in
   let x = caten x y in
   let x = pack x (function (mult, n) -> mult * n) in
   x;;
   
 let nt_hex_dot = caten dot nt_hex_float_natural;;
   
 let nt_hex_float = 
   let i = nt_hex_integer in
   let d = nt_hex_dot in
   let x = caten i d in
   pack x (function (integer,(dott,s))->
     if (integer > 0) then
       ((float_of_string (String.concat "" [string_of_int integer ;".0"])) +. s)
     else
       ((float_of_string (String.concat "" [string_of_int integer ;".0"])) -. s));;
 
 let nt_number_hex =
   let integer_caster = pack nt_hex_integer (fun x -> Number(Int (x))) in
   let float_caster = pack nt_hex_float (fun y -> Number(Float(y))) in
   disj float_caster integer_caster;;
 
 let nt_number=
   let x = caten number_hex_pre nt_number_hex in
   let x = pack x (fun (pre, num) -> num) in
   (rest (disj_list [x; nt_decimal_number_with_extention; nt_decimal_number]) (disj nt_bool nt_symbol));;
         (* --------------------------------------Char-------------------------------------- *)
 let nt_char_visible = const (fun ch -> ch > ' ');;
 
 let nt_char_named = 
   let null = pack (word_ci "nul") (fun _ -> (char_of_int 0)) in
   let newline = pack (word_ci "newline") (fun _ -> (char_of_int 10)) in
   let return = pack (word_ci "return") (fun _ -> (char_of_int 13)) in
   let tab = pack (word_ci "tab") (fun _ -> (char_of_int 9)) in
   let page = pack (word_ci "page") (fun _ -> (char_of_int 12)) in
   let space = pack (word_ci "space") (fun _ -> (char_of_int 32)) in
   disj_list [null; newline; return; tab; page; space];;
 
 let nt_hex_ascii= 
   let h = plus hex_digit in
   pack h (fun (s) -> char_of_int(int_of_string (String.concat "" ["0x" ; (list_to_string s)])));;
 
 let nt_char_hex =
   let x = hex_pre in
   let y = nt_hex_ascii in
   let z = caten x y in  
   pack z (function (t,ascii)-> ascii);;
 
 let nt_small_char = 
   let y = disj_list [nt_char_named; nt_char_hex; nt_char_visible] in
   let x = caten (word "#\\") y in
   pack x (fun (_,a) -> a);;
 
 let nt_char = pack nt_small_char (fun (ch) -> Char (ch));;
         (* --------------------------------------String-------------------------------------- *)
 let nt_string_pre_hex_char = pack (word "\\x") (fun _ -> true);;
 
 let string_hex_char =
   let nt_hex_chars = plus hex_digit in
   let x = caten (caten (word_ci "\\x") nt_hex_chars) (char ';') in
   let x = pack x (fun ((_,a),_) -> nt_hex_ascii a) in
   let x = pack x (fun (a,_) -> a) in
   x;;
 
 let string_meta_char = 
   let a = pack (word "\\\\") (fun _ -> '\\') in
   let b = pack (word "\\\"") (fun _ -> '\"') in
   let c = pack (word "\\t") (fun _ -> '\t') in
   let d = pack (word "\\f") (fun _ -> '\012') in
   let e = pack (word "\\n") (fun _ -> '\n') in
   let f = pack (word "\\r") (fun _ -> '\r') in
   disj_list [a;b;c;d;e;f];;
 
 let nt_string_literal_char = 
   let x = diff nt_any (one_of "\\\"") in
   x;;
 
 let string_char = 
   disj_list [string_hex_char; string_meta_char; nt_string_literal_char];;
 
 let nt_string =
   let s_chars = star string_char in
   let quote = (char '\"') in 
   let x = caten (caten quote s_chars) quote in
   let y = pack x (fun ((lq, p), rq) -> String (list_to_string p)) in
   y;;
 
 let comment_symbol = pack (word "#;") (fun _ -> true);;
 
   (* --------------------------------------Quotes-------------------------------------- *)
 let rec nt_list s =
   let list_of_sexps = star nt_sexp in
   let x = make_enclosed lparen list_of_sexps rparen in
   let y = make_enclosed lbar list_of_sexps rbar in
   let x = disj x y in
   let y = pack x (fun ss -> 
   match ss with
     [] -> Nil
     |_ -> List.fold_right (fun z w-> Pair (z,w)) 
     ss 
     Nil) in
   y s
 
   and only_dots_handler s = 
     let (dots, rest) = (word "...") s in
     nt_sexp rest
 
 and nt_list_balanced_helper (p,r) =
   match r with
   ['.';'.';'.'] -> (p,[])
   |_ -> (p,r)
 
 and nt_list_balanced_paren s =
   let s = s @ ['.';'.';'.'] in
   let list_of_sexps = star nt_sexp in
   let dots = (word "...") in
   let x = caten (caten lparen list_of_sexps) dots in
   let z = caten (caten lbar list_of_sexps) dots in
   let x = disj x z in
   let y = pack x (fun ((lpar, sexps), dots) -> 
   match sexps with
     [] -> Nil
     |_ -> List.fold_right (fun z w-> Pair (z,w)) 
     sexps 
     Nil) in
   nt_list_balanced_helper (y s)
 
 and nt_dotted_list s =
   let list_of_sexps = plus nt_sexp in
   let x = (caten (caten (caten (caten lparen list_of_sexps) (char '.')) nt_sexp) rparen) in
   let y = (caten (caten (caten (caten lbar list_of_sexps) (char '.')) nt_sexp) rbar) in
   let z = disj x y in
   let x = pack z (fun ((((lp,first_exps),dot),last_exp),rp) -> List.fold_right (fun a b -> Pair (a,b)) first_exps last_exp) in
   x s
 
 and nt_dotted_list_balanced s = 
   let s = s @ ['.';'.';'.'] in
   let list_of_sexps = star nt_sexp in
   let dots = (word "...") in
   let x = caten (caten (caten (caten lparen list_of_sexps) (char '.')) nt_sexp) dots in
   let y = caten (caten (caten (caten lbar list_of_sexps) (char '.')) nt_sexp) dots in
   let x = disj x y in
   let y = pack x (fun ((((lp, first_exps), dot), last_exp), dots) -> List.fold_right (fun a b -> Pair (a,b)) first_exps last_exp) in
   nt_list_balanced_helper (y s)
 
 and nt_quoted s =
   let x = caten (char '\'') nt_sexp in
   let y = pack x (fun (quote, rest) -> Pair(Symbol "quote", Pair(rest, Nil))) in
   y s
 
 and nt_qquoted s = 
   let x = caten (char '`') nt_sexp in
   let y = pack x (fun (quote, rest) -> Pair(Symbol "quasiquote", Pair(rest, Nil))) in
   y s
 
 and nt_unquoted_spliced s = 
   let x = caten (word ",@") nt_sexp in
   let y = pack x (fun (quote, rest) -> Pair(Symbol "unquote-splicing", Pair(rest, Nil))) in
   y s
 
 and nt_unquoted s = 
   let x = caten (char ',') nt_sexp in
   let y = pack x (fun (quote, rest) -> Pair(Symbol "unquote", Pair(rest, Nil))) in
   y s
 
 and nt_vector s = 
   let list_of_sexps = star nt_sexp in
   let rparen = (char ')') in
   let x = caten (caten (word "#(") list_of_sexps) rparen in
   let y = pack x (fun ((pre, sexps), rp) -> Vector sexps) in
   y s
 
 (* --------------------------------------sexp_comment-------------------------------------- *)
 
 and make_enclosed l p r =
   let enclosed = caten (caten l p) r in
   let x = pack enclosed (fun ((left, pi), right) -> pi) in
   x
 
 and nt_white =
   let x = const (fun ch -> ch <= ' ') in
   let x = pack x (fun _ -> ()) in
   x
 
 and nt_line_comment  = 
   let x = char ';' in
   let y = const (fun ch -> ch <> '\n') in
   let x = caten x (star y) in 
   let y = disj (pack (char '\n')(fun _ -> [])) nt_end_of_input in
   let x = caten x y in
   let x = pack x (fun _ -> ()) in
   x  
 
 and nt_sexp_comment s =
   let x = caten (word "#;") nt_sexp in
   let x = pack x (fun _ -> ()) in
   x s
 
 and nt_comment s =
   disj nt_line_comment nt_sexp_comment s
 
 and nt_skip s =
   let x = disj nt_white nt_comment in
   let x = star x in
   x s
 
 and make_nt___p___ nt_p =
   let x = caten nt_skip nt_p in
   let x = caten x nt_skip in
   let x = pack x (fun ((_, e), _) -> e) in
   x
 
 and nt_nil s =
   let x = caten (char '(') nt_skip in
   let x = caten x (char ')') in
   let x = pack x (fun _ -> Nil) in
   make_nt___p___ x s
 
 and rec_reader x = 
   match nt_sexp x with
     (y,[]) -> [y]
     | (y, ['.';'.';'.']) -> [y]
     | (y,z) -> y :: (rec_reader z)
 
   (* --------------------------------------sexp-------------------------------------- *)
 and nt_sexp sexp = 
   let x = disj_list [nt_bool; nt_number; nt_char; nt_list; nt_dotted_list; nt_vector; nt_quoted; nt_qquoted; nt_unquoted_spliced; nt_unquoted; nt_string; nt_list_balanced_paren; nt_dotted_list_balanced; nt_symbol; nt_nil; only_dots_handler] in
   nt_list_balanced_helper (make_nt___p___  x sexp);;
 
 let read_sexpr string =
   let x = string_to_list string in
   match nt_sexp x with
     |(y,[])-> y
     |(y,['.';'.';'.']) -> y
     |_ -> raise X_no_match;;
 
 let read_sexprs string = 
   let x = string_to_list string in
   match x with
   []->[]
   |_-> rec_reader x;;
 
 end;;
