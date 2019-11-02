(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;
 open PC;;
 
 type var = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | Const' Void, Const' Void -> true
   | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
   | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
   | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
   | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
   | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
   | Applic'(e1, args1), Applic'(e2, args2)
   | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (List.for_all2 expr'_eq args1 args2)
   | _ -> false;;
         
 exception X_syntax_error;;
 
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 
 (* let annotate_lexical_addresses e = raise X_not_yet_implemented;;
 
 let annotate_tail_calls e = raise X_not_yet_implemented;;
 
 let box_set e = raise X_not_yet_implemented;;

 let run_semantics expr = raise X_not_yet_implemented;;

 end;; *)
  (* struct Semantics *)

 let rec run_semantics expr =
   box_set
     (annotate_tail_calls
        (annotate_lexical_addresses expr))
 
 and annotate_lexical_addresses s = 
   annotate_helper (s,[],[])
 
 and annotate_helper (s,bound_list, params_list) = 
   match s with
     If (test, dit, dif) -> If'((annotate_helper (test,bound_list, params_list)),
                                (annotate_helper (dit, bound_list, params_list)),
                                (annotate_helper (dif, bound_list, params_list)))
     | Const x -> Const' x
     | Seq x -> Seq' (List.map (fun curr -> (annotate_helper (curr, bound_list, params_list))) x)
     | Set (x,y) -> Set' ((annotate_helper (x, bound_list, params_list)), (annotate_helper (y, bound_list, params_list)))
     | Def (x,y) -> Def' ((annotate_helper (x, bound_list, params_list)), (annotate_helper (y, bound_list, params_list)))
     | Or x -> Or' (List.map (fun curr -> (annotate_helper (curr, bound_list, params_list))) x)
     | LambdaSimple (params, body) -> LambdaSimple' (params, (annotate_helper (body, params_list::bound_list, params)))
     | LambdaOpt (params, last_param, body) -> LambdaOpt'(params, last_param, (annotate_helper (body, params_list::bound_list, params @ [last_param])))
     | Var x -> (var_handler (x, bound_list, params_list))
     | Applic (x,y) -> Applic' ((annotate_helper (x, bound_list, params_list)), (List.map (fun curr -> (annotate_helper (curr, bound_list, params_list))) y))
     (* | _ -> raise X_syntax_error *)
     
 and var_handler (s, bound_list, params_list) = 
   try Var'(VarParam(s,find_param(s, params_list, 0))) with
     X_no_match -> (try Var'(VarBound(s,find_array_index(s, bound_list, 0), find_array_inner_index(s, bound_list))) with
       X_no_match -> Var'(VarFree(s)))
 
 and find_array_index (s, bound_list, i) = 
   match bound_list with
     [] -> raise X_no_match
     | hd :: tl -> try (if(find_param(s,hd,0)>=0) 
                        then i 
                        else raise X_no_match)
                   with X_no_match -> find_array_index (s, tl, i+1)
 
 and find_array_inner_index (s, bound_list) = 
   match bound_list with
     [] -> raise X_no_match
     | hd :: tl -> try (find_param(s,hd,0)) with
                     X_no_match -> find_array_inner_index (s, tl)
 
 and find_param (s, params_list, i) =
   match params_list with
     [] -> raise X_no_match
     | hd :: tl -> (if (String.equal s hd) 
                   then i 
                   else find_param (s, tl, i+1))
 
  and annotate_tail_calls s = 
  (annotate_tail_calls_helper (s, false))

  and annotate_tail_calls_helper (s, b)=
    match s with
    If' (test, dit, dif) -> If'((annotate_tail_calls_helper (test, false)), (annotate_tail_calls_helper (dit, b)),(annotate_tail_calls_helper (dif, b))) 
    | Const' x -> s
    | Seq' x -> Seq' (List.mapi (fun i curr -> if (i <> (List.length x) -1) then (annotate_tail_calls_helper (curr, false)) else (annotate_tail_calls_helper (curr, true))) x)
    | Set' (x,y) -> Set' ((annotate_tail_calls_helper (x, false)), (annotate_tail_calls_helper (y, false)))
    | Def' (x,y) -> Def' ((annotate_tail_calls_helper (x, false)), (annotate_tail_calls_helper (y, false)))
    | Or' x -> Or' (List.mapi (fun i curr -> if (i <> (List.length x) -1) then (annotate_tail_calls_helper (curr, false)) else (annotate_tail_calls_helper (curr, b))) x)
    | LambdaSimple' (params, body) -> LambdaSimple' (params, (annotate_tail_calls_helper (body, true)))
    | LambdaOpt' (params, last_param, body) -> LambdaOpt'(params, last_param, (annotate_tail_calls_helper (body, true)))
    | Var' x -> s
    | Applic' (x,y) ->
      let (z,w) = ((annotate_tail_calls_helper (x, false)), (List.map (fun curr -> (annotate_tail_calls_helper (curr, false))) y)) in
      if (not b) then (Applic' (z,w)) else (ApplicTP'(z,w))                 
    | _-> raise X_no_match

(* returns false only if one of the lists is empty or lists are equals *)
  and lambdas_lists_check (read, write) = 
    match read with
      [] -> false
      |_ -> (match write with
              [] -> false
              |_ -> if (not((lambdas_lists_check_oneSide(read, write)) && (lambdas_lists_check_oneSide(write, read)))) 
                      then true 
                      else check_if_two_similarities((clear_duplicates(read, [])), (clear_duplicates(write, [])),0)) 
                      (* else false) *)

(* returns true only if first C_ second *)
  and lambdas_lists_check_oneSide (first, second) = 
    match first with
      [] -> true
      | hd :: tl -> (match List.exists (fun x -> hd == x) second with
                        false -> false
                        |_ -> lambdas_lists_check_oneSide(tl, second))

  and clear_duplicates (list, args) = 
    match list with
      [] -> args
      | hd :: tl -> (match List.exists (fun x -> hd == x) args with
                      false -> clear_duplicates (tl, hd::args)
                      | true -> clear_duplicates (tl, args))

  and check_if_two_similarities (list1, list2, counter) = 
    match list1 with
      [] -> (if (counter > 1) then true else false)
      | hd :: tl -> (match List.exists (fun x -> hd == x) list2 with
                      false -> check_if_two_similarities (tl, list2, counter)
                      | true -> check_if_two_similarities (tl, list2, counter+1))

  and box_set (expr') = 
    match expr' with
      If' (test, dit, dif) -> If'((box_set test), (box_set dit), (box_set dif))
      | Const' x -> expr'
      | Seq' x -> Seq' (List.map (fun curr -> (box_set curr)) x)
      | Set' (x,y) -> Set' ((box_set x), (box_set y))
      | Def' (x,y) -> Def' ((box_set x), (box_set y))
      | Or' x -> Or' (List.map (fun curr -> (box_set curr)) x)
      | Var' x -> expr'
      | Applic' (x,y) -> Applic' ((box_set x), (List.map (fun curr -> (box_set curr)) y))
      | ApplicTP' (x,y) -> ApplicTP' ((box_set x), (List.map (fun curr -> (box_set curr)) y))
      | Box' x -> expr'
      | BoxGet' x -> expr'
      | BoxSet' (x,y) -> BoxSet' (x, (box_set y))
      | LambdaSimple' (params, body) -> LambdaSimple' (params, (box_set_lambda_args_helper (params, 0, body, expr')))
      | LambdaOpt' (params, last_param, body) -> LambdaOpt' (params, last_param, (box_set_lambda_args_helper (params @ [last_param], 0, body, expr')))

    (* returns the body *)
and box_set_lambda_args_helper (params, minor, body, origin_lambda) = 
  match params with
    [] -> (box_set body)
    | hd :: tl -> box_set_lambda_args_helper(tl, minor+1, box_set_lambda_helper(hd, minor, body, origin_lambda), origin_lambda)

(* 1st stage : check appearances of each variable *)
(* 2nd stage : call lambdas_lists_check and check wether to box or not *)
(* 3rd stage : do the boxing if needed *)
(* 4th stage : call box_set on the lambda's body *)

 (* need to return the body *)
and box_set_lambda_helper (var, minor, body, origin_lambda) =
  if (lambdas_lists_check(rw_helper (body, [], [], var, -1, origin_lambda)))
      then do_the_boxing (var, minor, body, origin_lambda)
      else body

and do_the_boxing (var, minor, body, origin_lambda) =
  let to_add = Set'(Var'(VarParam(var, minor)), Box'(VarParam(var, minor))) in
  match body with
    Seq' x -> 
       (match (List.nth x 0) with
        Set'(_, Box'(_)) -> box_gs_helper((Seq' (do_the_boxing_seq_helper (x, to_add))), var, -1)
        |_ -> box_gs_helper((Seq' (to_add::[body])), var, -1) )
    | _ -> box_gs_helper((Seq' (to_add::[body])), var, -1)

and do_the_boxing_seq_helper (body, to_add) = 
  match List.hd body with 
    Set' (_, Box' (_)) -> [List.hd body]@do_the_boxing_seq_helper(List.tl body, to_add)
    |_ -> [to_add]@(body)

and rw_helper (s ,r_list, w_list, var_to_find, lambda_counter, first_lambda) = 
  match s with
  If' (test, dit, dif) -> rw_if_helper (test, dit, dif, r_list, w_list, var_to_find, lambda_counter, first_lambda)
  | Const' x -> (r_list, w_list)
  | Seq' x -> rw_list_helper (x, r_list, w_list, var_to_find, lambda_counter, first_lambda)
  | Def' (x,y) -> rw_pair_helper(x, y, r_list, w_list, var_to_find, lambda_counter, first_lambda)
  | Or' x -> rw_list_helper (x, r_list, w_list, var_to_find, lambda_counter, first_lambda)
  | LambdaSimple' (params, body) -> 
    if (lambda_counter = -1) then rw_helper (body ,r_list, w_list, var_to_find, lambda_counter+1, s)
    else rw_helper (body ,r_list, w_list, var_to_find, lambda_counter+1, first_lambda)
  | LambdaOpt' (params, last_param, body) -> 
    if (lambda_counter = -1) then rw_helper (body ,r_list, w_list, var_to_find, lambda_counter+1, s)
    else rw_helper (body ,r_list, w_list, var_to_find, lambda_counter+1, first_lambda)
  | Var' x -> 
      (match s with
        Var'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_find && x_mj=lambda_counter) then (r_list@[first_lambda], w_list) else (r_list, w_list)
        | Var'(VarParam (x_name,x_mn)) -> if (x_name=var_to_find && lambda_counter= -1) then (r_list@[first_lambda], w_list) else (r_list, w_list)
        | _ -> (r_list, w_list))
  | BoxGet' x-> 
    (match s with
    BoxGet'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_find && x_mj=lambda_counter) then (r_list@[first_lambda], w_list) else (r_list, w_list)
      | BoxGet'(VarParam (x_name,x_mn)) -> if (x_name=var_to_find && lambda_counter= -1) then (r_list@[first_lambda], w_list) else (r_list, w_list)
      | _ -> (r_list, w_list))
  | Set' (x,y)-> 
      let (y_r,y_w)= rw_helper (y ,r_list, w_list, var_to_find, lambda_counter, first_lambda) in
      let (x_r, x_w)= (match x with
        Var'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_find && x_mj=lambda_counter) then (r_list, w_list@[first_lambda]) else (r_list, w_list)
        | Var'(VarParam (x_name,x_mn)) -> if (x_name=var_to_find && lambda_counter= -1) then (r_list, w_list@[first_lambda]) else (r_list, w_list)
        | _ -> (r_list, w_list)) in
        (x_r @ y_r, x_w @ y_w)
  | BoxSet' (x,y)-> 
      let (y_r,y_w)= rw_helper (y ,r_list, w_list, var_to_find, lambda_counter, first_lambda) in
      let (x_r, x_w)= (match x with
        (VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_find && x_mj=lambda_counter) then (r_list, w_list@[first_lambda]) else (r_list, w_list)
        | (VarParam (x_name,x_mn)) -> if (x_name=var_to_find && lambda_counter= -1) then (r_list, w_list@[first_lambda]) else (r_list, w_list)
        | _ -> (r_list, w_list)) in
        (x_r @ y_r, x_w @ y_w)
  | Box' x ->
    (match s with
        Box'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_find && x_mj=lambda_counter) then (r_list@[first_lambda], w_list) else (r_list, w_list)
        | Box'(VarParam (x_name,x_mn)) -> if (x_name=var_to_find && lambda_counter= -1) then (r_list@[first_lambda], w_list) else (r_list, w_list)
        | _ -> (r_list, w_list))
  | Applic' (x,y) -> rw_axlist_helper (x, y, r_list, w_list, var_to_find, lambda_counter, first_lambda)        
  | ApplicTP' (x,y) -> rw_axlist_helper (x, y, r_list, w_list, var_to_find, lambda_counter, first_lambda)  

and rw_if_helper (test, dit, dif, r_list, w_list, var_to_find, lambda_counter, first_lambda) =
  (let (test_r, test_w) = (rw_helper (test, r_list, w_list, var_to_find, lambda_counter, first_lambda)) in
  let (dit_r, dit_w) = (rw_helper (dit, r_list, w_list, var_to_find, lambda_counter,first_lambda)) in
  let (dif_r,dif_w) = (rw_helper (dif, r_list, w_list, var_to_find, lambda_counter,first_lambda)) in
  let if_r = test_r @ dit_r @ dif_r in
  let if_w = test_w @ dit_w @ dif_w in
  (if_r, if_w))

and rw_pair_helper (x, y, r_list, w_list, var_to_find, lambda_counter,first_lambda) =
  let (x_r, x_w) = (rw_helper (x, r_list, w_list, var_to_find, lambda_counter,first_lambda)) in
  let (y_r, y_w) = (rw_helper (y, r_list, w_list, var_to_find, lambda_counter,first_lambda)) in
  let (res_r,res_w) = (x_r @ y_r, x_w @ y_w) in
  (res_r,res_w)

and rw_list_helper (x, r_list, w_list, var_to_find, lambda_counter,first_lambda) =
  let res_lists = (List.map (fun curr -> (rw_helper (curr, r_list, w_list, var_to_find, lambda_counter,first_lambda))) x) in
  let (res_r, res_w) = List.fold_left (fun (a,b) (c,d)-> (a@c,b@d))([],[]) res_lists in
  (res_r, res_w)

and rw_axlist_helper (x, y, r_list, w_list, var_to_find, lambda_counter,first_lambda) = 
  let (x_r, x_w) = (rw_helper (x, r_list, w_list, var_to_find, lambda_counter,first_lambda)) in
  let y_lists = (List.map (fun curr -> (rw_helper (curr, r_list, w_list, var_to_find, lambda_counter,first_lambda))) y) in
  let (y_r, y_w) = List.fold_left (fun (a,b) (c,d)-> (a@c,b@d))([],[]) y_lists in
  let (res_r, res_w) = (x_r @ y_r, x_w @ y_w) in
  (res_r, res_w)

  and box_gs_helper (s ,var_to_box_gs, lambda_counter) = 
    match s with 
      If' (test, dit, dif) -> 
        If'((box_gs_helper (test, var_to_box_gs, lambda_counter)),(box_gs_helper (dit, var_to_box_gs, lambda_counter)),(box_gs_helper (dif, var_to_box_gs, lambda_counter)))
      | Const' x -> s
      | Seq' x -> Seq' (List.map (fun curr -> (box_gs_helper (curr, var_to_box_gs, lambda_counter))) x)
      | Def' (x,y) -> Def' ((box_gs_helper (x, var_to_box_gs, lambda_counter)),(box_gs_helper (y, var_to_box_gs, lambda_counter)))
      | Or' x -> Or' (List.map (fun curr -> (box_gs_helper (curr, var_to_box_gs, lambda_counter))) x)
      | LambdaSimple' (params, body) -> 
        if (lambda_counter = -1) then LambdaSimple' (params, (box_gs_helper (body ,var_to_box_gs, lambda_counter+1)))
        else LambdaSimple' (params, (box_gs_helper (body ,var_to_box_gs, lambda_counter+1)))
      | LambdaOpt' (params, last_param, body) -> 
        if (lambda_counter = -1) then LambdaOpt' (params, last_param, (box_gs_helper (body ,var_to_box_gs, lambda_counter+1)))
        else LambdaOpt' (params, last_param, (box_gs_helper (body ,var_to_box_gs, lambda_counter+1)))
      | Var' x -> 
          (match s with
            Var'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_box_gs && x_mj=lambda_counter) then BoxGet'(VarBound (x_name,x_mj,x_mn)) else Var'(VarBound (x_name,x_mj,x_mn))
            | Var'(VarParam (x_name,x_mn)) -> if (x_name=var_to_box_gs && lambda_counter= -1) then BoxGet'(VarParam (x_name,x_mn)) else Var'(VarParam (x_name,x_mn))
            | _ -> Var'(x))
      | Box' _ | BoxGet' _ -> s

      | BoxSet' (x,y) -> 
          let box_gs_y = (box_gs_helper (y, var_to_box_gs, lambda_counter)) in
          (match x with
          VarBound (x_name,x_mj,x_mn) -> if (x_name=var_to_box_gs && x_mj=lambda_counter) then BoxSet'((VarBound (x_name,x_mj,x_mn)),box_gs_y) else BoxSet'(VarBound (x_name,x_mj,x_mn),box_gs_y)
          | VarParam (x_name,x_mn) -> if (x_name=var_to_box_gs && lambda_counter= -1 && y<>Box'(VarParam(x_name,x_mn))) then BoxSet'((VarParam (x_name,x_mn)),box_gs_y) else BoxSet'(VarParam (x_name,x_mn),box_gs_y)
          | _ -> BoxSet' (x, box_gs_y) ) 
          (* BoxSet' (x, box_gs_y)  *)

      | Set' (x,y) -> 
          let box_gs_y = (box_gs_helper (y, var_to_box_gs, lambda_counter)) in
          (match x with
          Var'(VarBound (x_name,x_mj,x_mn)) -> if (x_name=var_to_box_gs && x_mj=lambda_counter) then BoxSet'((VarBound (x_name,x_mj,x_mn)),box_gs_y) else Set'(x,box_gs_y)
          | Var'(VarParam (x_name,x_mn)) -> if (x_name=var_to_box_gs && lambda_counter= -1 && y<>Box'(VarParam(x_name,x_mn))) then BoxSet'((VarParam (x_name,x_mn)),box_gs_y) else Set'(Var'(VarParam (x_name,x_mn)),box_gs_y)
          | _ -> Set' (x, box_gs_y) ) 

      | Applic' (x,y) -> Applic'((box_gs_helper (x, var_to_box_gs, lambda_counter)),(List.map (fun curr -> (box_gs_helper (curr, var_to_box_gs, lambda_counter))) y))        
      | ApplicTP' (x,y) -> ApplicTP'((box_gs_helper (x, var_to_box_gs, lambda_counter)),(List.map (fun curr -> (box_gs_helper (curr, var_to_box_gs, lambda_counter))) y))  

 end;;
