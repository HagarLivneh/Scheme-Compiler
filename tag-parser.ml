(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "reader.ml";;
 open PC;;
 
 type constant =
   | Sexpr of sexpr
   | Void
 
 type expr =
   | Const of constant
   | Var of string
   | If of expr * expr * expr
   | Seq of expr list
   | Set of expr * expr
   | Def of expr * expr
   | Or of expr list
   | LambdaSimple of string list * expr
   | LambdaOpt of string list * string * expr
   | Applic of expr * (expr list);;
 
 let rec expr_eq e1 e2 =
   match e1, e2 with
   | Const Void, Const Void -> true
   | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
   | Var(v1), Var(v2) -> String.equal v1 v2
   | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                             (expr_eq th1 th2) &&
                                               (expr_eq el1 el2)
   | (Seq(l1), Seq(l2)
     | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
   | (Set(var1, val1), Set(var2, val2)
     | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                              (expr_eq val1 val2)
   | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
   | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr_eq body1 body2)
   | Applic(e1, args1), Applic(e2, args2) ->
      (expr_eq e1 e2) &&
        (List.for_all2 expr_eq args1 args2)
   | _ -> false;;
   
                        
 exception X_syntax_error;;
 
 module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
 end;; (*signature TAG_PARSER*)
 
 module Tag_Parser : TAG_PARSER = struct
 
 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;  
 
 (* work on the tag parser starts here *)
(*   
let tag_parse_expression sexpr = raise X_not_yet_implemented;;
 
let tag_parse_expressions sexpr = raise X_not_yet_implemented;;
 (* struct Tag_Parser *)
 end;;   *)

 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;

let var_tp_helper s = 
  match (List.mem s reserved_word_list) with
  false -> Var(s)
  |true -> raise X_syntax_error;;

let var_tp s = 
  match s with
  Pair(Symbol("unquote"), Pair(Symbol(x), Nil)) -> var_tp_helper x
  | Symbol(x) -> var_tp_helper x
  |_-> raise X_syntax_error;;
 
 let const_tp s =
   match s with
   Pair(Symbol("quote"), Pair(x,Nil)) -> Const(Sexpr(x))
   | Number(x) -> Const(Sexpr(Number(x)))
   | Bool(x) -> Const(Sexpr(Bool(x)))
   | Char(x) -> Const(Sexpr(Char(x)))
   | String(x) -> Const(Sexpr(String(x)))
   |_-> raise X_syntax_error;;

   let disj_tp tp1 tp2 =
    fun s ->
    try (tp1 s)
    with X_syntax_error -> (tp2 s);;
  
  let tp_none _ = raise X_syntax_error;;
    
  let disj_tp_list tps = List.fold_right disj_tp tps tp_none;;
 
   let rec tag_parse s =
     disj_tp_list [const_tp; var_tp; if_tp; set_tp; seq_tp; def_tp; or_tp; lambdaSimple_tp; lambdaOpt_tp;
      and_macro; mit_define_macro; let_rec_macro; let_star_macro; let_macro; cond_macro; quasiquote_macro; app_tp] s
 
 and if_tp s = 
   match s with
     Pair(Symbol("if"), Pair(test, Pair(dit, Pair(c, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse c)
     | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const(Void))
     |_-> raise X_syntax_error
   
   and begin_tp_helper s = 
     match s with
       Pair(Symbol("begin"), Pair(a,Nil)) -> [(tag_parse a)]
       | Pair(Symbol("begin"), Pair(a,b)) -> (tag_parse a) :: (begin_tp_helper (Pair(Symbol("begin"), b)))
       | Pair(Symbol("begin"), Nil) -> [Const(Void)]
       |_ -> raise X_syntax_error
   
   and list_tp_helper s = 
     match s with
     Pair(a,Nil) -> [(tag_parse a)]
     | Pair(a,b) -> (tag_parse a) :: (list_tp_helper b)
     |_ -> raise X_syntax_error
   
   and seq_tp s = 
     let x = begin_tp_helper s in
     match x with
     [a]->a
     |_ -> Seq(x)
 
 and set_tp s = 
   match s with
     Pair(Symbol("set!"), Pair(x,Pair(y,Nil))) -> Set(var_tp x, tag_parse y)
     |_ -> raise X_syntax_error
 
 and def_tp s = 
   match s with
     Pair(Symbol("define"), Pair(x,Pair(y,Nil))) -> Def(var_tp x, tag_parse y)
     |_ -> raise X_syntax_error
 
 and or_tp s = 
   match s with
     Pair(Symbol("or"), Nil) -> const_tp(Bool (false))
     |Pair(Symbol("or"), Pair(a, Nil)) -> (tag_parse a)
     |Pair(Symbol("or"), x) -> Or(list_tp_helper x)
     |_ -> raise X_syntax_error
 
 and app_tp s = 
   match s with
     Pair(a,Nil) -> Applic(tag_parse a, [])
     | Pair(a,b) -> Applic(tag_parse a, (list_tp_helper b))
     |_ -> raise X_syntax_error
 
 and lambdaSimple_tp_args_helper s = 
   match s with 
     Pair(Symbol x, Nil) -> [x]
     | Pair(Symbol x, b) -> x :: (lambdaSimple_tp_args_helper b)
     |_ -> raise X_syntax_error

 and lambdaSimple_check_args_validation s =
    match s with
      [] -> s
      | head::tail -> match (is_member head tail) with
                        false -> head::(lambdaSimple_check_args_validation tail)
                        | _ -> raise X_syntax_error
    
 and is_member s list =
    match list with
    | [] -> false
    | head::tail ->
          if head=s 
            then true
            else (is_member s tail)

 and lambdaSimple_tp_body_helper s = 
   match s with
     Pair(a,Nil) -> (tag_parse a)
     | Pair(a,b) -> Seq(list_tp_helper s)
     | _ -> raise X_syntax_error
 
 and lambdaSimple_tp s = 
   match s with
     Pair(Symbol("lambda"), Pair(args, body))->
       (match args with
         Pair(Symbol x, _) -> LambdaSimple((lambdaSimple_check_args_validation(lambdaSimple_tp_args_helper args)), (lambdaSimple_tp_body_helper body))
         |Nil -> LambdaSimple([],(lambdaSimple_tp_body_helper body))
         |_ -> raise X_syntax_error)
     |_ -> raise X_syntax_error
 
 and lambdaOpt_list_tp_helper s = 
   match s with
     Pair(a, Pair(b,c)) -> (tag_parse a) :: (lambdaOpt_list_tp_helper (Pair(b,c)))
     | Pair(a,b) -> [(tag_parse a)]
     |_ -> raise X_syntax_error
 
     (* lambdaOpt_tp_args_helper avoids the last argument!!!!!! *)
 and lambdaOpt_tp_args_helper s = 
   match s with 
     Pair(Symbol x, Symbol y) -> [x]
     | Pair(Symbol x, b) -> x :: (lambdaOpt_tp_args_helper b)
     |_ -> raise X_syntax_error
 
 and lambdaOpt_args_last_element s = 
   match s with 
     Pair(Symbol x, Symbol y) -> y
     | Pair(Symbol x, Pair(b,c)) -> (lambdaOpt_args_last_element (Pair(b,c)))
     | Symbol x -> x
     |_ -> raise X_syntax_error

 and lambdaOpt_check_args_validation list last_arg =
    (lambdaSimple_check_args_validation (List.append list last_arg))

 and lambdaOpt_tp s = 
   match s with
     Pair(Symbol("lambda"), Pair(Nil, body)) -> 
     LambdaOpt([],"" ,(lambdaSimple_tp_body_helper body))
     | Pair(Symbol("lambda"), Pair(Symbol x, body)) ->
     LambdaOpt([],(lambdaOpt_args_last_element (Symbol x)),(lambdaSimple_tp_body_helper body))
     | Pair(Symbol("lambda"), Pair(args, body)) -> (
        match (lambdaOpt_check_args_validation (lambdaOpt_tp_args_helper args) [(lambdaOpt_args_last_element args)]) with
        x ->
        LambdaOpt((lambdaOpt_tp_args_helper args),(lambdaOpt_args_last_element args),(lambdaSimple_tp_body_helper body)))
     |_ -> raise X_syntax_error
 
 and and_macro s=
   match s with
     Pair(Symbol("and"), Nil) -> const_tp(Bool (true))
     | Pair(Symbol("and"), Pair(a, Nil)) -> (tag_parse a)
     | Pair(Symbol("and"), Pair(a,b)) ->
     let f_arg = (const_tp (Bool (false))) in
     If ((tag_parse a), (tag_parse (Pair((Symbol("and")), b))), f_arg)
     |_ -> raise X_syntax_error
 
and mit_define_macro s=
   match s with
    Pair(Symbol("define"), Pair(Pair((Symbol var), Nil), exprs)) -> Def ((tag_parse (Symbol var)), tag_parse (Pair (Symbol("lambda"), Pair (Nil, exprs))))
    | Pair(Symbol("define"), Pair(Pair(var, Nil), exprs)) -> raise X_syntax_error
    | Pair(Symbol("define"), Pair(Pair(var, arglist), exprs)) ->
        Def ((tag_parse var), tag_parse (Pair (Symbol("lambda"), Pair (arglist, exprs))))
    |_ -> raise X_syntax_error
 
and let_macro s =
  match s with
    Pair(Symbol("let"), x)-> (let_macro_helper x)
    |_ -> raise X_syntax_error
 
 and let_macro_helper s = 
   match s with
     Pair(Nil,body) -> Applic(LambdaSimple([], (lambdaSimple_tp_body_helper body)), [])
     |Pair(varvals,body) -> (
      let args = (let_tp_args_helper varvals) in
      let vals = (let_tp_vals_helper varvals) in
      Applic(LambdaSimple(args, (lambdaSimple_tp_body_helper body)), vals)
     )
   |_-> raise X_syntax_error
 
 and let_tp_args_helper s = 
       match s with 
       Pair(Pair(Symbol arg, _), Nil) -> [arg]
       | Pair (Pair (Symbol arg, _), rest)-> arg :: (let_tp_args_helper rest)
       |_ -> raise X_syntax_error 
 
 and let_tp_vals_helper s = 
   match s with 
     Pair(Pair(Symbol arg, Pair(v,Nil)), Nil) -> [tag_parse v]
     |Pair(Pair(Symbol arg, Pair(v,Nil)), rest)-> (tag_parse v) :: (let_tp_vals_helper rest)
     |_ -> raise X_syntax_error
 
 and let_star_macro s =
   match s with
     Pair(Symbol("let*"), x)-> (let_star_macro_helper x)
     |_ -> raise X_syntax_error
 
 and let_star_macro_helper s =
     match s with
       Pair(Nil, body)-> let_macro (Pair(Symbol("let"), s)) (*empty base case*)
       |Pair(varval,body)->  
         (match varval with
           Pair(Pair(Symbol arg1, _), Nil)-> 
             let_macro (Pair(Symbol("let"), s))(*one arg base case*)
           |Pair (first_arg, rest_args)-> 
           let_macro (Pair(Symbol("let"),  Pair(Pair(first_arg,Nil), Pair(Pair(Symbol ("let*"), Pair(rest_args, body)), Nil))))
           |_ -> raise X_syntax_error
           )
       |_ -> raise X_syntax_error

                                  
 and let_rec_macro s =
   match s with
     Pair(Symbol("letrec"), x)-> (let_rec_macro_helper x)
     |_ -> raise X_syntax_error
 
 and let_rec_macro_helper s = 
     match s with
     Pair(Nil, body)-> let_macro (Pair(Symbol("let"), s)) (* empty base case *)
     |Pair(varval, body)->
       (let args = let_rec_tp_args_helper varval in
        let sets = let_rec_tp_vals_helper s in
             let_macro (Pair(Symbol("let"),  Pair(args ,sets))))
      |_ -> raise X_syntax_error
 
   
 and let_rec_tp_args_helper s = 
     match s with 
       Pair(Pair(Symbol arg, _), Nil) -> Pair(Pair ((Symbol arg) , Pair(Pair(Symbol "quote", Pair (Symbol "whatever", Nil)),Nil)), Nil)
       | Pair (Pair (Symbol arg, _), rest)-> Pair (Pair ((Symbol arg ), Pair(Pair(Symbol "quote", Pair (Symbol "whatever", Nil)),Nil)),(let_rec_tp_args_helper rest))
       |_ -> raise X_syntax_error
 
 and let_rec_tp_vals_helper s =
     match s with 
       Pair(Pair(Pair(Symbol arg, Pair(v,Nil)), Nil),body) -> Pair(Pair(Symbol("set!"), Pair((Symbol arg) , Pair(v,Nil))) , body)
       | Pair(Pair (Pair (Symbol arg, Pair(v,Nil)), rest),body)-> Pair(Pair(Symbol("set!"), Pair((Symbol arg) ,Pair(v,Nil))), (let_rec_tp_vals_helper (Pair(rest,body))))
       |_ -> raise X_syntax_error
 
  and cond_macro s = 
    match s with
      Pair(Symbol "cond", Pair(Pair(x,Nil),Nil)) -> (tag_parse x)
      | Pair(Symbol "cond", x) -> (cond_macro_cases_helper x)
      |_ -> raise X_syntax_error
     
  and cond_macro_cases_helper s = 
    match s with
      Pair(Pair(Symbol "else", Pair(a,Nil)), _) -> (tag_parse a)
      | Pair(Pair(Symbol "else", Pair(a,b)), _) -> (seq_tp (Pair(Symbol "begin",Pair(a,b))))
      | Pair(Pair(test1, Pair(Symbol "=>", then1)),Nil) ->
      (let_macro (Pair (Symbol "let",
          Pair
          (Pair (Pair (Symbol "value", Pair (test1, Nil)),
            Pair
              (Pair (Symbol "f",
                Pair
                (Pair (Symbol "lambda",
                  Pair (Nil,
                    then1)),
                Nil)),
              Nil)),
          Pair
            (Pair (Symbol "if",
              Pair (Symbol "value",
              Pair (Pair (Pair(Symbol "f",Nil), Pair (Symbol "value", Nil)),
                Nil))),
            Nil)))))
      | Pair(Pair(test1, Pair(Symbol "=>", then1)),rest1) ->
          (let_macro (Pair (Symbol "let",
          Pair
          (Pair (Pair (Symbol "value", Pair (test1, Nil)),
            Pair
              (Pair (Symbol "f",
                Pair
                (Pair (Symbol "lambda",
                  Pair (Nil,then1)),
                Nil)),
              Pair
              (Pair (Symbol "rest",
                Pair
                  (Pair (Symbol "lambda",
                    Pair (Nil,
                    Pair(Pair(Symbol "cond", rest1),Nil))),
                  Nil)),
              Nil))),
          Pair
            (Pair (Symbol "if",
              Pair (Symbol "value",
              Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                Pair (Pair (Symbol "rest", Nil), Nil)))),
            Nil)))))       
      | Pair(Pair(test,Pair(dit,Nil)),Nil) ->
          If((tag_parse test), (tag_parse dit), (Const(Void)))
      | Pair(Pair(test,Pair(dit1,dit2)),Nil) ->
          If((tag_parse test), (seq_tp (Pair(Symbol "begin", Pair(dit1,dit2)))), (Const(Void)))
      | Pair(Pair(test,Pair(dit,Nil)),dif) ->
          If((tag_parse test), (tag_parse dit), (tag_parse (Pair(Symbol "cond", dif))))
      | Pair(Pair(test,Pair(dit1,dit2)),dif) ->
          If((tag_parse test), (seq_tp (Pair(Symbol "begin", Pair(dit1,dit2)))), (tag_parse (Pair(Symbol "cond", dif))))
      |_ -> raise X_syntax_error
       
and quasiquote_macro s = 
    match s with
       Pair(Symbol "quasiquote", Pair(a, Nil)) -> (tag_parse (quasiquote_macro_helper (a)))
      | _ -> raise X_syntax_error


and quasiquote_macro_helper s =
    match s with
      Pair (Symbol "unquote", Pair(x, Nil))-> (x)
     | Pair (Symbol "unquote-splicing", x)-> raise X_syntax_error
     | Pair (Symbol "quote", Pair(x, Nil))-> (quasiquote_macro_pair_handler s)
     | Vector(x) -> Pair (Symbol("vector"), (quasiquote_macro_vector_handler x))
     | Pair (Pair(a,b), Nil)-> (quasiquote_macro_pair_handler s)
     | Pair (a, Pair(b,c))-> (quasiquote_macro_pair_handler s)
     | x -> Pair(Symbol "quote", Pair(x, Nil))
    
     and quasiquote_macro_pair_handler s =
     match s with 
       Pair(Pair(Symbol "unquote-splicing", Pair (a, Nil)), Nil)->(* (,@a  Nil)*)
           Pair(Symbol "append", Pair(a,(Pair((quasiquote_macro_pair_handler Nil),Nil))))
      
       | Pair(Pair(Symbol "unquote-splicing", Pair(a,Nil)), Pair(b,c))->(* (,@a  b)*)
           Pair(Symbol "append", Pair(a,(Pair((quasiquote_macro_pair_handler (Pair(b,c))),Nil))))
       
       | Pair(Symbol "unquote-splicing", Pair(a,Nil)) -> (* (. ,@a)*)
           a
   
       | Pair(Pair(Symbol "unquote", Pair(a,Nil)), Nil)-> (* (,a  Nil)*)
           Pair(Symbol "cons", Pair(a,(Pair((quasiquote_macro_pair_handler Nil),Nil))))
   
       | Pair(Pair(Symbol "unquote", Pair(a,Nil)), Pair(b,c))-> (* (,a  b)*)
           Pair(Symbol "cons", Pair(a,(Pair((quasiquote_macro_pair_handler (Pair(b,c))),Nil))))
   
       | Pair(Symbol "unquote", Pair(a,Nil)) -> (* (. ,a)*)
           a
   
       | Pair(a, Nil) -> (* (a)*) 
           Pair(Symbol "cons", Pair((quasiquote_macro_pair_handler a),(Pair((quasiquote_macro_pair_handler Nil),Nil))))
   
       | Pair(a, Pair(b,c)) -> (* (a  b)*) 
           Pair(Symbol "cons", Pair((quasiquote_macro_pair_handler a),(Pair((quasiquote_macro_pair_handler (Pair(b,c))),Nil))))
         
       | Pair(a, b) -> (* (a . b)*)
           Pair(Symbol "cons", Pair((quasiquote_macro_pair_handler a),(Pair((quasiquote_macro_pair_handler b),Nil))))
   
       | Nil ->  (* end of list*)
           Pair (Symbol "quote", Pair (Nil, Nil))

       | Vector(a) -> (* (. a)*)
            quasiquote_macro_helper(Vector (a))
   
       | a -> (* (. a)*)
           Pair(Symbol "quote", (Pair(a,Nil)))


and quasiquote_macro_vector_handler s =
List.fold_right (fun x y -> Pair((quasiquote_macro_helper x) ,y)) s Nil;;

let tag_parse_expression sexpr = tag_parse sexpr;;
 
let tag_parse_expressions sexpr = List.map tag_parse sexpr;;
 (* struct Tag_Parser *)
 end;;
