#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> int -> string-> int -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  (* let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
 end;;  *)

 let rec make_consts_tbl asts =
  let const_tbl = [ (Void, (0, "MAKE_LITERAL_VOID"));
                    (Sexpr Nil, (1, "MAKE_LITERAL_NIL"));
                    (Sexpr(Bool false), (2, "MAKE_LITERAL_BOOL(0)"));
                    (Sexpr(Bool true), (4, "MAKE_LITERAL_BOOL(1)"))] in
  match asts with
    [] -> []
    |_ -> make_consts_tbl_helper (asts, const_tbl)

    (* return const_table *)
and make_consts_tbl_not_const_helper (ast, const_tbl) = 
  match ast with
    If' (test, dit, dif) -> make_consts_tbl_helper ([test;dit;dif], const_tbl)
    | Seq' x -> make_consts_tbl_helper (x, const_tbl)
    | Set' (x,y) -> make_consts_tbl_helper ([x;y], const_tbl)
    | Def' (x,y) -> make_consts_tbl_helper ([x;y], const_tbl)
    | Or' x -> make_consts_tbl_helper (x, const_tbl)
    | LambdaSimple' (params,body) -> make_consts_tbl_helper([body], const_tbl)
    | LambdaOpt' (params, last_param, body) -> make_consts_tbl_helper ([body], const_tbl)
    | Applic' (x,y) -> make_consts_tbl_helper ([x]@y, const_tbl)
    | ApplicTP' (x,y) -> make_consts_tbl_helper ([x]@y, const_tbl)
    | BoxSet' (var,body) -> make_consts_tbl_helper ([body], const_tbl)
    | _ -> const_tbl



and make_consts_tbl_helper (asts, const_tbl) = 
  match asts with 
    [] -> const_tbl
    |hd :: tl -> (match hd with
          Const'(Void) ->   if (check_const_if_exist (Void, const_tbl))
                            then make_consts_tbl_helper (tl, const_tbl)
                            else make_consts_tbl_helper (tl, const_tbl @ [(Void, (extract_last_offset (const_tbl), "MAKE_LITERAL_VOID"))])

          | Const'(Sexpr Nil) -> if (check_const_if_exist (Sexpr Nil, const_tbl))
                                  then make_consts_tbl_helper (tl, const_tbl)
                                  else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Nil), (extract_last_offset (const_tbl), "MAKE_LITERAL_NIL"))])

          | Const'(Sexpr(Bool true)) -> if (check_const_if_exist (Sexpr(Bool true), const_tbl)) 
                                          then make_consts_tbl_helper (tl, const_tbl) 
                                          else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Bool true), (extract_last_offset (const_tbl), "MAKE_LITERAL_BOOL(1)"))])

          | Const'(Sexpr(Bool false)) -> if (check_const_if_exist (Sexpr(Bool false), const_tbl)) 
                                           then make_consts_tbl_helper (tl, const_tbl) 
                                           else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Bool false), (extract_last_offset (const_tbl), "MAKE_LITERAL_BOOL(0)"))])
              
          | Const'(Sexpr(Char y)) -> if (check_const_if_exist (Sexpr(Char y), const_tbl))
                                      then make_consts_tbl_helper (tl, const_tbl)
                                      else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Char y), (extract_last_offset (const_tbl), "MAKE_LITERAL_CHAR("^string_of_int (Char.code y)^")"))])

          | Const'(Sexpr(Number(Int y))) -> if (check_const_if_exist (Sexpr(Number (Int y)), const_tbl))
                                            then make_consts_tbl_helper (tl, const_tbl)
                                            else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Number(Int y)), (extract_last_offset (const_tbl), "MAKE_LITERAL_INT("^(string_of_int y)^")"))])
                                
          | Const'(Sexpr(Number(Float y))) -> if (check_const_if_exist (Sexpr(Number (Float y)), const_tbl))
                                              then make_consts_tbl_helper (tl, const_tbl)
                                              else make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(Number(Float y)), (extract_last_offset (const_tbl), "MAKE_LITERAL_FLOAT("^(string_of_float y)^")"))])

          | Const'(Sexpr(String y)) ->  if (check_const_if_exist (Sexpr(String y), const_tbl))
                                          then make_consts_tbl_helper (tl, const_tbl)
                                          else (
                                            let str = string_to_list y in
                                            let str = List.map (fun x -> int_of_char x) str in
                                            let as_string = String.concat ", " (List.map (fun x -> string_of_int x) str) in
                                            let asm_command = "MAKE_LITERAL_STRING "^ string_of_int (List.length str) ^ ", " ^ as_string in
                                            make_consts_tbl_helper (tl, const_tbl @ [(Sexpr(String y), (extract_last_offset (const_tbl), asm_command))]))

          | Const'(Sexpr(Symbol y)) -> make_consts_tbl_helper (tl, symbol_handler (Sexpr(Symbol y), const_tbl))

          | Const'(Sexpr(Pair(a,b))) -> make_consts_tbl_helper (tl, pair_handler (Sexpr(Pair(a,b)), const_tbl))

          | Const'(Sexpr(Vector x)) -> make_consts_tbl_helper (tl, vector_handler (Sexpr(Vector x), const_tbl))

          |_ -> make_consts_tbl_helper (tl, make_consts_tbl_not_const_helper(hd, const_tbl))
                  )

and vector_handler (e, const_tbl) =
  match e with 
    Sexpr(Vector x) ->
      (let y = List.map (fun z -> Const' (Sexpr z)) x in
      let table = make_consts_tbl_helper (y,const_tbl) in
      let asm_command = vector_handler_string_helper(x, table, "MAKE_LITERAL_VECTOR "^ string_of_int (List.length x)) in
      table @ [e, (extract_last_offset (table), asm_command)])
    |_ -> raise X_no_match

and vector_handler_string_helper (e, const_tbl, str) =
  match e with
    [] -> str
    | a::[] -> str ^ ", const_tbl+" ^ get_offset_as_string (Sexpr a, const_tbl)
    | a::b -> (let x = str ^ ", const_tbl+" ^ get_offset_as_string (Sexpr a, const_tbl) in
              vector_handler_string_helper (b, const_tbl, x))

and pair_handler (e, const_tbl) = 
  match e with
    Sexpr(Pair(a,Nil)) -> if (check_const_if_exist(e,const_tbl))
                    then const_tbl
                    else (let x = make_consts_tbl_helper ([Const'(Sexpr(Nil)); Const' (Sexpr a)], const_tbl) in
                           x @ [(Sexpr(Pair(a,Nil)), (extract_last_offset (x), "MAKE_LITERAL_PAIR(const_tbl+"^get_offset_as_string (Sexpr a, x)^", const_tbl+"^get_offset_as_string (Sexpr(Nil), x)^")"))])
    |Sexpr(Pair (a,b)) -> if (check_const_if_exist(e,const_tbl))
                    then const_tbl
                    else (let x = pair_handler (Sexpr b, const_tbl) in
                          let y = make_consts_tbl_helper ([Const' (Sexpr a)], x) in
                        y @ [(Sexpr(Pair(a,b)), (extract_last_offset (y), "MAKE_LITERAL_PAIR(const_tbl+"^get_offset_as_string (Sexpr a, y)^", const_tbl+"^get_offset_as_string (Sexpr b, y)^")"))])
    |a -> make_consts_tbl_helper([Const' a], const_tbl)

and symbol_handler (e, const_tbl) = 
  match e with
    Sexpr(Symbol y) -> 
      if (check_const_if_exist (Sexpr (String y), const_tbl))
      then (
          if (check_const_if_exist (Sexpr(Symbol y), const_tbl))
            then const_tbl
            else const_tbl @ [(Sexpr(Symbol y), (extract_last_offset (const_tbl), "MAKE_LITERAL_SYMBOL const_tbl+"^get_offset_as_string (Sexpr(String y), const_tbl)))]
      )
      else (let x = make_consts_tbl_helper ([Const' (Sexpr (String y))], const_tbl) in
            x @ [(Sexpr(Symbol y), (extract_last_offset(x), "MAKE_LITERAL_SYMBOL const_tbl+"^get_offset_as_string (Sexpr (String y), x)))])
      | _ -> raise X_no_match
    
and get_offset_as_string (arg, table) = 
  match List.find (fun (a,(b,c)) -> a=arg) table with
    (_, (offset, _)) -> string_of_int offset

and check_const_if_exist (arg, table) =
  List.exists (fun x -> x=true) (List.map (fun (a,(b,c)) -> if(a=arg) then true else false) table)

and extract_last_offset (table) = 
  match table with
    [] -> 0
    | (name,(offset,_)) :: [] -> 
        (match name with
          Void -> offset + 1
          | Sexpr (Nil) -> offset + 1
          | Sexpr (Bool _) -> offset + 2
          | Sexpr (Char _) -> offset + 2
          | Sexpr (Number _) -> offset + 9
          | Sexpr (String x) -> offset + 9 + (String.length x)
          | Sexpr (Pair (_,_)) -> offset + 17
          | Sexpr (Symbol x) -> offset + 9
          | Sexpr (Vector x) -> offset + 9 + 8*(List.length x)
        )
    | hd :: tl -> extract_last_offset (tl);;

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
      "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
      "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
      "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
      "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
      "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
      "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
      "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
      "car","my_car";"cdr","my_cdr";"set-car!", "car_set";"set-cdr!","cdr_set";"cons","my_cons"
      (* you can add yours here *)];;

let rec make_fvars_tbl asts =
(make_fvars_tbl_helper (asts, (prims_fvar_tbl (primitive_names_to_labels, 0))))

and prims_fvar_tbl (tbl, counter) =
  match tbl with
  []-> []
  | (label, prim)::tl-> [(label, counter)] @  (prims_fvar_tbl (tl, counter + 1))

and make_fvars_tbl_helper (arg, fvar_table) =
  (match arg with
    []-> fvar_table
    | hd::tl-> 
    let head = (match hd with
    If' (test, dit, dif) -> (make_fvars_tbl_helper ([test;dit;dif] ,fvar_table)) 
    | Const' x -> fvar_table
    | Seq' x -> (make_fvars_tbl_helper (x, fvar_table))
    | Set' (x,y) -> (make_fvars_tbl_helper ([x;y], fvar_table)) 
    | Def' (x,y) -> (make_fvars_tbl_helper ([x;y], fvar_table))
    | Or' x -> (make_fvars_tbl_helper (x, fvar_table))
    | Var'(VarFree x)-> 
    (if (check_fvar_if_exist (x,fvar_table)) then fvar_table 
    else (fvar_table @ [make_fvar_tuple (x, fvar_table)]))
    | Var'(_)-> fvar_table
    | Applic' (x,y) -> (make_fvars_tbl_helper ([x] @ y, fvar_table))
    | ApplicTP' (x,y) -> (make_fvars_tbl_helper ([x] @ y, fvar_table))
    | Box' x -> (make_fvars_tbl_helper ([Var'(x)], fvar_table))
    | BoxGet' x -> (make_fvars_tbl_helper ([Var'(x)], fvar_table))
    | BoxSet' (x,y) ->  (make_fvars_tbl_helper ([Var'(x);y], fvar_table))
    | LambdaSimple' (params, body) -> (make_fvars_tbl_helper ([body], fvar_table))
    | LambdaOpt' (params, last_param, body) -> (make_fvars_tbl_helper ([body], fvar_table))) 

    in (make_fvars_tbl_helper (tl, head)))


and make_fvar_tuple (arg_name, table)= 
  let a = arg_name in 
  let index_of_last = (List.length table - 1) in
  let b = (index_of_last + 1) in
  (a, b)


and check_fvar_if_exist (arg, table) = 
  List.exists (fun x-> x = true) (List.map (fun (a,b)->
  if(a = arg) then true else false) table)

and find_prim_label (x,lst) =
    match lst with
    [] -> raise X_no_match
    | (h1,h2)::t -> if x = h1 then h2 else (find_prim_label (x,t))

and find_fvar_offset (x,lst) =
    match lst with
    [] -> raise X_no_match
    | (h1,h2)::t -> if x = h1 then h2 else (find_fvar_offset (x,t))

 let rec generate consts fvars lambda_count label_str count e = 
    match e with
      Const' e -> 
        ";CONST\n"^
        "\tmov rax, const_tbl+" ^ get_offset_as_string (e , consts) ^"\n"
      | Var'(VarParam(_, minor))-> 
        ";VAR_PARAM\n"^(*4=old_rbp+return_address+lex_env+num_of_args*)
        "\tmov rax, qword [rbp + 8 * (4 +"^(string_of_int minor)^")]\n"
      | Var'(VarFree(v))-> 
        ";VAR_FREE\n"^
        "\tmov rax, qword [fvar_tbl + "^(string_of_int (find_prim_label(v,fvars)))^"*WORD_SIZE]\n"
      | Var'(VarBound(_, major, minor))->
        ";VAR_BOUND\n"^
        "\tmov rax, qword [rbp + 8 * 2]\n"^
        "\tmov rax, qword [rax + 8 *"^ (string_of_int major)^"]\n"^
        "\tmov rax, qword [rax + 8 *"^ (string_of_int minor)^"]\n"
      | Set'(Var'(VarParam(_, minor)),e)-> 
        ";SET_VAR_PARAM\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) e )^
        "\tmov qword [rbp + 8 * (4 + "^(string_of_int minor)^")], rax\n"^
        "\tmov rax, SOB_VOID_ADDRESS\n"
      | Set'(Var'(VarFree(v)),e)->
        ";SET_VAR_FREE\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) e)^
        "\tmov qword [fvar_tbl + "^(string_of_int (find_prim_label(v,fvars)))^"*WORD_SIZE], rax\n"^
        "\tmov rax, SOB_VOID_ADDRESS\n"
      | Set'(Var'(VarBound(_,major,minor)),e)->
        ";SET_VAR_BOUND\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) e)^
         "\tmov rbx, qword [rbp + 8 * 2]\n"^
         "\tmov rbx, qword [rbx + 8 * "^(string_of_int major)^"]\n"^
         "\tmov qword [rbx + 8 *"^(string_of_int minor)^"], rax\n"^
         "\tmov rax, SOB_VOID_ADDRESS\n"
      | Def'(Var'(VarFree(v)),e)->
        ";DEF_VAR_FREE\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) e)^
        "\tmov qword [fvar_tbl + "^(string_of_int (find_prim_label(v,fvars)))^"*WORD_SIZE], rax\n"^
        "\tmov rax, SOB_VOID_ADDRESS\n"
      | Seq'(e)-> 
        ";SEQ\n"^(String.concat "" (List.mapi (fun i x-> (generate consts fvars lambda_count (label_str^"x"^(string_of_int (count + i))) (count + (i + 1)) x)) e))
      | Or'(e)-> 
        let seperator = "\tcmp rax, SOB_FALSE_ADDRESS\n\tjne Lorexit"^label_str^"\n" in
        ";OR\n"^(String.concat seperator (List.mapi (fun i x-> (generate consts fvars lambda_count (label_str^"x"^(string_of_int (count + i))) (count + (i +1)) x)) e)) ^
        "Lorexit"^label_str^":\n"
      | If'(test,dit,dif)->
        (* (if_label_inc()) *)
        ";IF\n"^ 
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) test)^
        "\tcmp rax, SOB_FALSE_ADDRESS\n"^
        "\tje Lelse"^(label_str^"x"^(string_of_int count))^"\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 2) dit)^
        "\tjmp Lifexit"^(label_str^"x"^(string_of_int count))^"\n"^
        "Lelse"^(label_str^"x"^(string_of_int count))^":\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 3) dif)^
        "Lifexit"^(label_str^"x"^(string_of_int count))^":\n"
      | Applic' (rator, rands) -> 
        ";APPLIC\n"^
        let rands = rands @ [Const'(Sexpr Nil)] in
        let rev_rands = (List.rev rands) in
        applic_helper (rev_rands, consts, fvars, lambda_count, (label_str^"x"^(string_of_int count)), count)^
        "\tpush " ^ (string_of_int (List.length rands))^ "\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) rator)^
(* Verify if rax has type closure *)
          (* "\tmov rsi, rax\n"^
          "\tmov bl, byte [rsi]\n"^
          "\tcmp bl, T_CLOSURE\n"^
          "\tjne .error\n"^     (* build .error label *)  *)
          (*  *)
          (* if it is a closure -> push the env to the stack and call the body *)
        
        "\n\tCLOSURE_ENV rbx, rax\n"^
        "\tpush rbx\n"^ (* push the lambda's env to the stuck *)
        "\tCLOSURE_CODE rbx, rax\n"^
        "\tcall rbx\n"^ (* call the lambda's body*)
        "\n\tadd rsp, 8*1\n"^
        "\tpop rbx\n"^
        "\tshl rbx, 3\n"^
        "\tadd rsp, rbx\n"
      | Box' (VarParam(_, minor)) ->
        ";BOX\n"^
        (* (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) (Var'(x)))^ *)
        (* "\tmov r12, rax\n"^ *)
        (* "\tMALLOC rax, 8\n"^
        "\tmov qword [rax], r12\n" *)
        "\tmov r12, [rbp + 8 * (4 + "^(string_of_int minor)^")]\n"^
        "\tMALLOC rbx, 8\n"^
        "\tmov qword [rbx], r12\n"^
        "\tmov rax, rbx\n"
      | BoxGet'(x)->
        ";BOXGET\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) (Var'(x)))^
        "\tmov rax, qword [rax]\n"
      | BoxSet'(x,e)->
        ";BOXSET\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) e)^
        "\tpush rax\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 2) (Var'(x)))^
        "\tpop qword [rax]\n"^
        "\tmov rax, SOB_VOID_ADDRESS\n"
      | LambdaSimple' (params, body)->
        ";LAMBDA_SIMPLE\n"^

        "\tMALLOC rax, "^(string_of_int ((lambda_count + 1)* 8))^"\n"^
        "\tmov rbx, rax\n"^ (*save the address of new lex_address created*)
        "\tmov qword [rbx], SOB_NIL_ADDRESS\n"^
        
        "\tmov r8, "^(string_of_int lambda_count)^"\n"^
        "\tcmp r8, qword 0\n"^
        "\tje Ldummy_frame"^label_str^"\n"^

        "\tmov rax, qword [rbp + 8 * 2]\n"^(*get old lexical address*)
        "\tmov r10, 0\n"^
        
        "Lcopy_pointers"^label_str^":\n"^
        "\tmov r11, [rax + 8 * r10]\n"^
        "\tinc r10\n"^
        "\tmov qword [rbx + 8 * r10], r11\n"^
        "\tcmp r10, "^(string_of_int (lambda_count + 1))^"\n"^
        "\tjne Lcopy_pointers"^label_str^"\n"^ 
        
        "\tmov r14, [rbp+ 24]\n"^
        "\tshl r14, 3\n"^
        "\tMALLOC rax, r14\n"^
        "\tmov r11, rax\n"^
        "\tmov [rbx], r11\n"^(*mov new allocated params to new_env[0]*)

        "\tmov r8, qword [rbp + 3 * 8]\n"^
        "\tcmp r8, 0\n"^
        "\tje Lno_more_args"^label_str^"\n"^

        "\tmov r10, 0\n"^
        "Lcopy_new_var_params"^label_str^":\n"^
        "\tmov r9, PVAR(r10)\n"^(*get next var_param*)
        "\tmov [rax + 8 * r10], qword r9\n"^
        "\tinc r10\n"^
        "\tcmp r10, qword r8\n"^
        "\tjne Lcopy_new_var_params"^label_str^"\n"^ 

        "Ldummy_frame"^label_str^":\n"^
        "Lno_more_args"^label_str^":\n"^
        "\tMAKE_CLOSURE(rax, rbx, Lcode"^label_str^" )\n"^
        "\tjmp Lcont"^label_str^"\n"^ 
        "Lcode"^label_str^":\n"^
        "\tpush rbp\n"^
        "\tmov rbp , rsp\n"^
        (generate consts fvars (lambda_count + 1) (label_str^"x"^(string_of_int count)) (count + 1) body)^
        "\tleave\n"^
        "\tret\n"^
        "Lcont"^label_str^":\n"
      | ApplicTP' (rator, rands) -> 
        (* "LApplicTP"^label_str^":\n"^ *)
        ";APPLIC_TP\n"^
        let rands = rands @ [Const'(Sexpr Nil)] in
        let rev_rands = (List.rev rands) in
        applic_helper (rev_rands, consts, fvars, lambda_count, (label_str^"x"^(string_of_int count)), count)^
        "\tpush " ^ (string_of_int (List.length rands))^ "\n"^
        (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) rator)^
        (* Verify if rax has type closure *)
        "\n\tCLOSURE_ENV rbx, rax\n"^
        "\tmov r10, rbx\n"^
        "\tpush qword r10\n"^ (*save env*)
        "\tmov r9, qword [rbp+ 8*1]\n"^
        "\tpush qword r9\n"^(*save return address*)
        "\tmov r8, qword [rbp]\n"^
        "\tpush qword r8\n"^(*save old rbp*)

        "\tSHIFT_FRAME "^(string_of_int ((List.length rands)))^"\n"^
    
        "\tCLOSURE_CODE rbx, rax\n"^
        "\tjmp rbx\n" (*call the lambda's body*)
        
      | LambdaOpt' (params, last_param, body) ->
        ";LAMBDA_OPT\n"^
(* EXTEND THE LEXICAL ADDRESS *)
        "\tMALLOC rax, "^(string_of_int ((lambda_count + 1)* 8))^"\n"^
        "\tmov rbx, rax\n"^ (*save the address of new lex_address created*)
        "\tmov qword [rbx], SOB_NIL_ADDRESS\n"^
        
        "\tmov r8, "^(string_of_int lambda_count)^"\n"^
        "\tcmp r8, qword 0\n"^
        "\tje Ldummy_frame"^label_str^"\n"^

        "\tmov rax, qword [rbp + 8 * 2]\n"^(*get old lexical address*)
        "\tmov r10, 0\n"^
        
        "Lcopy_pointers"^label_str^":\n"^
        "\tmov r11, [rax + 8 * r10]\n"^
        "\tinc r10\n"^
        "\tmov qword [rbx + 8 * r10], r11\n"^
        "\tcmp r10, "^(string_of_int (lambda_count + 1))^"\n"^
        "\tjne Lcopy_pointers"^label_str^"\n"^ 
        
        "\tmov r14, [rbp + 8 * 3]\n"^
        "\tshl r14, 3\n"^
        "\tMALLOC rax, r14\n"^
        "\tmov r11, rax\n"^
        "\tmov [rbx], r11\n"^(*mov new allocated params to new_env[0]*)

        "\tmov r8, qword [rbp + 3 * 8]\n"^
        "\tcmp r8, 0\n"^
        "\tje Lno_more_args"^label_str^"\n"^
(* COPY OLD PARAMS TO NEW LEXICAL ADDRESS *)
        "\tmov r10, 0\n"^
        "Lcopy_new_var_params"^label_str^":\n"^
        "\tmov r9, PVAR(r10)\n"^(*get next var_param*)
        "\tmov [rax + 8 * r10], qword r9\n"^
        "\tinc r10\n"^
        "\tcmp r10, qword r8\n"^
        "\tjne Lcopy_new_var_params"^label_str^"\n"^ 

        "Ldummy_frame"^label_str^":\n"^
        "Lno_more_args"^label_str^":\n"^
        "\tMAKE_CLOSURE(rax, rbx, Loptcode"^label_str^" )\n"^
        "\tjmp Loptcont"^label_str^"\n"^ 

        "Loptcode"^label_str^":\n"^
        "\tmov r8, qword [rsp+ 8 * 2]\n"^(*num of args from applic*)
        "\tdec r8\n"^
        "\tmov r9, qword "^string_of_int (List.length params)^"\n"^(*num of must args from lambda*)
        "\tmov rbx, r8\n"^
        "\tmov r12, r8\n"^
        "\tsub r12, r9\n"^(*gap between params lengthes*)
 
        "\tmov rax, SOB_NIL_ADDRESS\n"^
        "\tadd rbx, 2\n"^ (*rbx <- (app_args) + 2)*)
        "\tcmp r12, 0\n"^
        "\tjle Laftermakelist"^label_str^"\n"^
        "Lmakelist"^label_str^":\n"^
          "\tmov r13, qword [rsp+8*rbx]\n"^ (*get next arg to pair*)
          "\tMAKE_PAIR(rdx, r13, rax)\n"^
          "\tmov rax, rdx\n"^
          "\tdec rbx\n"^
          "\tdec r12\n"^
          "\tcmp r12, 0\n"^
          "\tjne Lmakelist"^label_str^"\n"^
        "\tmov rbx, r9\n"^
        "\tmov qword [rsp+8*(rbx+3)], rax\n"^

        "Laftermakelist"^label_str^":\n"^
        "\tmov r15, qword [rsp + 8*2]\n"^	(*R15 <- app args*)
        "\tdec r15\n"^ (*cause of magic*)
        "\tmov r12, r15\n"^
        "\tmov r14, "^ string_of_int ((List.length params)+1) ^"\n"^		(* R14 <- lambda args *)
        "\tsub r12, r14\n"^	(* R12 <- app_args - lambda_args (# of shifts) *)
        "\tcmp r12, 1\n"^
        "\tjle Llambdaopt_end"^label_str^"\n"^	(* if app_args < lambda_args, do nothing *)

        "\tmov r13, r14\n"^
        "\tadd r13, 2\n"^		(* R13 <- Copy from*)
        "\tmov r9, "^ string_of_int ((List.length params)+1) ^"\n"^  
        "\tadd r9, 3\n"^    (* R9  <- How much copies*)
        "\tadd r15, 2\n"^   (* R15 <- Copy to*)
        "Llambdaopt_repeat"^label_str^":\n"^
          "\tmov r10, qword [rsp+8*r13]\n"^
          "\tmov qword [rsp+8*r15], r10\n"^
          "\tdec r13\n"^
          "\tdec r15\n"^
          "\tdec r9\n"^
          "\tcmp r9, 0\n"^
          "\tjne Llambdaopt_repeat"^label_str^"\n"^
        
        "\tinc r15\n"^
        "\tshl r15, 3\n"^
        "\tadd rsp, r15\n"^
        "\tmov r14, qword "^ string_of_int ((List.length params)+2) ^"\n"^
        "\tmov [rsp + 8*2], r14\n"^

        "Llambdaopt_end"^label_str^":\n"^
        "\tnop\n"^

        "\tpush rbp\n"^
        "\tmov rbp , rsp\n"^
        (generate consts fvars (lambda_count + 1) (label_str^"x"^(string_of_int count)) (count + 1) body)^
        "\tleave\n"^
        "\tret\n"^
        "Loptcont"^label_str^":\n"

      |_ -> raise X_no_match
      
  and applic_helper (rands, consts, fvars, lambda_count, label_str, count) =
    match rands with
      [] -> ""
      | hd::[] ->   (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) hd)^
                    "\tpush rax\n"
      | hd::tl ->  (generate consts fvars lambda_count (label_str^"x"^(string_of_int count)) (count + 1) hd)^
                    "\tpush rax\n"^
                    applic_helper (tl, consts, fvars, lambda_count, (label_str^"x"^(string_of_int count)), count + 1)

 (* let kaki = (List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs "((lambda (x) ((lambda () (set! x 4)))((lambda () x))) 5)")));; *)
end;;