open Scala_spec;;
open Format;;
open X86_64

(* Variables Globales de compilation *)
let l_str_id = ref [];;

let str_id_compt = ref 0;;

let and_id_compt = ref 0;;

let or_id_compt = ref 0;;

let if_id_compt = ref 0;;

let while_id_compt = ref 0;;

let mes_objets = Hashtbl.create 17;;




(* Initialisation de la partie donnée du programme, notamment des chaines de caractères *)
let init_data () =
  let rec loop l =
    match l with
    |[] -> X86_64.nop
    |head::tail ->
      (X86_64.label (fst head)) ++
      (X86_64.string_no_format (snd head)) ++
      (loop tail)
  in
  (X86_64.label "message_printf_int") ++
  (X86_64.string "%d") ++
  (loop (!l_str_id))
;;



let find_offset_members obj str =
  let rec loop l i =
    match l with
    |[] -> -1
    |head::tail ->
      if head.var_id = str then
        i
      else
        loop tail (i + 8)
  in
  loop obj.class_members 8
;;

let find_offset_methods obj str =
  let rec loop l i =
    match l with
    |[] -> -1
    |head::tail ->
      if head.method_id = str then
        i
      else
        loop tail (i + 8)
  in
  loop obj.class_methods 8
;;

let rec depil_car_loc var_loc out =
  match var_loc with
  |[] -> out
  |head::tail ->
    if fst head = "" then
      out
    else
      depil_car_loc tail (out ++ (X86_64.popq r11))
;;

let rec compile_expr e_dec var_loc meth =
  if Scala_type.string_of_type e_dec.e_ty = "Array" then
     X86_64.nop
  else
  match e_dec.desc with
  |EInteger(i) ->
    X86_64.movq (X86_64.imm i) (X86_64.reg rdi)
  |EString(str) ->
    l_str_id := ((sprintf "__STRING__%d" !str_id_compt), str)::(!l_str_id);
    str_id_compt := !str_id_compt + 1;
    X86_64.movq (X86_64.ilab (fst (List.hd !l_str_id))) (X86_64.reg rdi)
  |EBool(b) ->
    if b then
      X86_64.movq (X86_64.imm 1) (X86_64.reg rdi)
    else
      X86_64.movq (X86_64.imm 0) (X86_64.reg rdi)
  |ENull ->
    X86_64.movq (X86_64.imm 0) (X86_64.reg rdi)
  |EThis ->
    let offset = List.assoc "this" var_loc in
    X86_64.movq (X86_64.ind ~ofs:offset rbp) (X86_64.reg rdi)
  |EUnit ->
    X86_64.movq (X86_64.imm 0) (X86_64.reg rdi)
  |EAccess(a) -> begin
    match a with
    |Access_Ident(str) ->
      let offset = List.assoc str var_loc in
      X86_64.movq (X86_64.ind ~ofs:offset rbp) (X86_64.reg rdi)
    |Access_Point(exp, str) ->
      let code_exp = compile_expr exp var_loc meth in
      let obj = Hashtbl.find mes_objets (Scala_type.string_of_type exp.e_ty) in
      let offset = find_offset_members obj str in
      code_exp ++
      (X86_64.movq (X86_64.ind ~ofs:offset rdi) (X86_64.reg rdi))
  end
  |EAffectation(a, exp) -> begin
    match a with
    |Access_Ident(str) ->
      let code_exp = compile_expr exp var_loc meth in
      let offset = List.assoc str var_loc in
      code_exp ++
      (X86_64.movq (X86_64.reg rdi) (X86_64.ind ~ofs:offset rbp))
    |Access_Point(exp2, str) ->
      let code_exp = compile_expr exp var_loc meth in
      let code_exp2 = compile_expr exp2 var_loc meth in
      let obj = Hashtbl.find mes_objets (Scala_type.string_of_type exp2.e_ty) in
      let offset = find_offset_members obj str in
      code_exp ++
      (X86_64.pushq (X86_64.reg rdi)) ++
      code_exp2 ++
      (X86_64.popq r15) ++
      (X86_64.movq (X86_64.reg r15) (X86_64.ind ~ofs:offset rdi))
  end
  |ECall(a_exp, a_id, arg_ty, l_exp) ->
    let rec compile_arguments l =
      match l with
      |[] -> X86_64.nop
      |head::tail ->
        let code_exp = compile_expr head var_loc meth in
        code_exp ++
        (X86_64.popq r15) ++
        (X86_64.pushq (X86_64.reg rdi)) ++
        (X86_64.pushq (X86_64.reg r15)) ++
        (compile_arguments tail)
    in
    let rec depile_arg l =
      match l with
      |[] -> (X86_64.popq rdi)
      |head::tail ->
        (X86_64.popq rdi) ++
        (depile_arg tail)
    in
    let code_exp = compile_expr a_exp var_loc meth in
    let obj = Hashtbl.find mes_objets (Scala_type.string_of_type a_exp.e_ty) in
    let offset = find_offset_methods obj a_id in
    code_exp ++
    (X86_64.pushq (X86_64.reg rdi)) ++
    (X86_64.pushq (X86_64.ind ~ofs:0 rdi)) ++
    (compile_arguments l_exp) ++
    (X86_64.popq r13) ++
    (X86_64.call_star (X86_64.ind ~ofs:offset r13)) ++
    (depile_arg l_exp) ++
    (X86_64.movq (X86_64.reg rax) (X86_64.reg rdi))
  |EInstanciation(str, arg_ty, l_exp) ->
    let rec init_arg_cons l_a cl l_p =
      match l_a, l_p with
      |[], [] -> X86_64.nop
      |head1::tail1, head2::tail2 ->
        let code_exp = compile_expr head1 var_loc meth in
        let offset = find_offset_members cl head2.param_id in
        code_exp ++
        (X86_64.popq r15) ++
        (X86_64.movq (X86_64.reg rdi) (X86_64.ind ~ofs:offset r15)) ++
        (X86_64.pushq (X86_64.reg r15)) ++
        (init_arg_cons tail1 cl tail2)
    in
    let obj = Hashtbl.find mes_objets str in
    (X86_64.movq (X86_64.imm ((List.length obj.class_members + 1) * 8)) (X86_64.reg rdi)) ++
    (X86_64.call "malloc") ++
    (X86_64.movq (X86_64.reg rax) (X86_64.reg r15)) ++
    (X86_64.movq (X86_64.ilab (sprintf "descr_%s" obj.class_id)) (X86_64.ind ~ofs:0 r15)) ++
    (X86_64.pushq (X86_64.reg r15)) ++
    (init_arg_cons l_exp obj obj.class_param) ++
    (X86_64.call (sprintf "__new__%s__" obj.class_id)) ++
    (X86_64.popq rdi)
  |ENot(exp) ->
    let code_exp = compile_expr exp var_loc meth in
    code_exp ++ (X86_64.notq (X86_64.reg rdi))
  |ENeg(exp) ->
    let code_exp = compile_expr exp var_loc meth in
    code_exp ++ (X86_64.negq (X86_64.reg rdi))
  |EOp(exp1, op, exp2) -> begin
    let code_exp1 = compile_expr exp1 var_loc meth in
    let code_exp2 = compile_expr exp2 var_loc meth in
    let code = code_exp1 ++
               (X86_64.pushq (X86_64.reg rdi)) ++
               code_exp2 ++
               (X86_64.popq r10)
    in         
    match op with
    |Op_Add ->
      code ++
      (X86_64.addq (X86_64.reg r10) (X86_64.reg rdi))
    |Op_Sub ->
      code ++
      (X86_64.subq (X86_64.reg rdi) (X86_64.reg r10)) ++
      (X86_64.movq (X86_64.reg r10) (X86_64.reg rdi))
    |Op_Mul ->
      code ++
      (X86_64.imulq (X86_64.reg r10) (X86_64.reg rdi))
    |Op_Div ->
      code ++
      (X86_64.movq (X86_64.reg r10) (X86_64.reg rax)) ++
      (X86_64.cqto) ++
      (X86_64.idivq (X86_64.reg rdi)) ++
      (X86_64.movq (X86_64.reg rax) (X86_64.reg rdi))
    |Op_Mod ->
      code ++
      (X86_64.movq (X86_64.reg r10) (X86_64.reg rax)) ++
      (X86_64.xorq (X86_64.reg rdx) (X86_64.reg rdx)) ++
      (X86_64.idivq (X86_64.reg rdi)) ++
      (X86_64.movq (X86_64.reg rdx) (X86_64.reg rdi))
    |Op_And ->
      let and_label = sprintf "__AND__%d" !and_id_compt in
      and_id_compt := !and_id_compt + 1;
      code_exp1 ++
      (X86_64.testq (X86_64.imm 1) (X86_64.reg rdi)) ++
      (X86_64.je and_label) ++
      code_exp2 ++
      (X86_64.label and_label)
    |Op_Or ->
      let or_label = sprintf "__OR__%d" !or_id_compt in
      or_id_compt := !or_id_compt + 1;
      code_exp1 ++
      (X86_64.testq (X86_64.imm 1) (X86_64.reg rdi)) ++
      (X86_64.jne or_label) ++
      code_exp2 ++
      (X86_64.label or_label)
    |Op_Physical_Eq |Op_Eq ->
      code ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg rdi)) ++
      (X86_64.sete (X86_64.reg dil))
    |Op_Physical_Ne |Op_Ne ->
      code ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg rdi)) ++
      (X86_64.setne (X86_64.reg dil))
    |Op_Less ->
      code ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg rdi)) ++
      (X86_64.setg (X86_64.reg dil))
    |Op_Less_Eq ->
      code ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg rdi)) ++
      (X86_64.setge (X86_64.reg dil))
    |Op_Greater ->
      code ++
      (X86_64.movq (X86_64.reg rdi) (X86_64.reg r11)) ++
      (X86_64.xorq (X86_64.reg rdi) (X86_64.reg rdi)) ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg r11)) ++
      (X86_64.setl (X86_64.reg dil))
    |Op_Greater_Eq ->
      code ++
      (X86_64.cmpq (X86_64.reg r10) (X86_64.reg rdi)) ++
      (X86_64.setle (X86_64.reg dil))
  end
  |EIfThenElse(exp1, exp2, exp3) ->
    let code_exp1 = compile_expr exp1 var_loc meth in
    let code_exp2 = compile_expr exp2 var_loc meth in
    let code_exp3 = compile_expr exp3 var_loc meth in
    let endif_label = sprintf "__ENDIF__%d" !if_id_compt in
    let else_label = sprintf "__ELSE__%d" !if_id_compt in
    if_id_compt := !if_id_compt + 1;
    code_exp1 ++
    (X86_64.testq (X86_64.imm 1) (X86_64.reg rdi)) ++
    (X86_64.je else_label) ++
    code_exp2 ++
    (X86_64.jmp endif_label) ++
    (X86_64.label else_label) ++
    code_exp3 ++
    (X86_64.label endif_label)
  |EWhile(exp1, exp2) ->
    let code_exp1 = compile_expr exp1 var_loc meth in
    let code_exp2 = compile_expr exp2 var_loc meth in
    let debwhile_label = sprintf "__DEBWHILE__%d" !while_id_compt in
    let endwhile_label = sprintf "__ENDWHILE__%d" !while_id_compt in
    while_id_compt := !while_id_compt + 1;
    code_exp1 ++
    (X86_64.testq (X86_64.imm 1) (X86_64.reg rdi)) ++
    (X86_64.je endwhile_label) ++
    (X86_64.label debwhile_label) ++
    code_exp2 ++
    code_exp1 ++
    (X86_64.testq (X86_64.imm 1) (X86_64.reg rdi)) ++
    (X86_64.jne debwhile_label) ++
    (X86_64.label endwhile_label) ++
    (X86_64.xorq (X86_64.reg rdi) (X86_64.reg rdi))
  |EReturn(exp) ->
    let code_exp = compile_expr exp var_loc meth in
    code_exp ++
    (depil_car_loc var_loc (X86_64.nop)) ++
    (X86_64.jmp (sprintf "__%s__METHOD__%s__END" meth.method_obj meth.method_id))
  |Eprint(exp) -> begin
    let code_exp = compile_expr exp var_loc meth in
    match exp.e_ty with
    |TInt ->
      code_exp ++
      (X86_64.movq (X86_64.reg rdi) (X86_64.reg rsi)) ++
      (X86_64.movq (X86_64.ilab "message_printf_int") (X86_64.reg rdi)) ++
      (X86_64.xorq (X86_64.reg rax) (X86_64.reg rax)) ++
      (X86_64.call "printf") ++
      (X86_64.xorq (X86_64.reg rdi) (X86_64.reg rdi))
    |TString ->
      code_exp ++
      (X86_64.xorq (X86_64.reg rax) (X86_64.reg rax)) ++
      (X86_64.call "printf") ++
      (X86_64.xorq (X86_64.reg rdi) (X86_64.reg rdi))
    |_ -> X86_64.nop
  end
  |EBlock(l_b) ->
    let rec compile_block l_b var_loc out =
      match l_b with
      |[] ->
        out ++
        (depil_car_loc var_loc (X86_64.nop))
      |head::tail -> begin
        match head with
        |Block_Var(v) ->
          let code =
            (compile_expr v.var_v var_loc meth) ++
            (X86_64.pushq (X86_64.reg rdi))
          in
          let offset = snd (List.hd var_loc) - 8 in
          compile_block tail ((v.var_id, offset)::var_loc) (out ++ code)
        |Block_Expr(exp) ->
          let code = compile_expr exp var_loc meth in
          compile_block tail var_loc (out ++ code)
      end
    in
    let offset =
      if var_loc = [] then
        0
      else if snd (List.hd var_loc) > 0 then
        0
      else
        snd (List.hd var_loc)
    in
    compile_block l_b (("", offset)::var_loc) X86_64.nop
;;




let compile_desc_class cl d =
  let rec loop l_meth out =
    match l_meth with
    |[] -> out
    |head::tail ->
      loop tail (out ++ (X86_64.address [(sprintf "__%s__METHOD__%s__" head.method_obj head.method_id)]))
  in
  loop cl.class_methods (d ++
                         X86_64.label (sprintf "descr_%s" cl.class_id) ++
                         (match cl.class_extend with
                          |TType(str, l_arg) -> X86_64.address [(sprintf "descr_%s" str)]
                          |_ -> X86_64.dquad [0]))
;;

let compile_cons_class cl =
  let rec remove_arg_cons l cl =
    let rec loop l arg_cons =
      match l with
      |[] -> []
      |h::t ->
        if List.mem h.var_id arg_cons then
          loop t arg_cons
        else
          h::(loop t arg_cons)
    in
    loop l (List.map (fun x -> x.param_id) cl.class_param)
  in
  let rec loop l_m =
    match l_m with
    |[] -> X86_64.nop
    |head::tail ->
      let code_exp = compile_expr head.var_v [("this", 16)] 
        {method_id = "";
         method_param_type = [];
         method_param = [];
         method_out_ty = TNone;
         method_body = {desc = ENull; loc = (Lexing.dummy_pos, Lexing.dummy_pos); e_ty = TNone;};
         method_override = false;
         method_obj = "";
         method_loc = (Lexing.dummy_pos, Lexing.dummy_pos);} in
      let offset = find_offset_members cl head.var_id in
      code_exp ++
      (X86_64.movq (X86_64.ind ~ofs:16 rbp) (X86_64.reg r14)) ++
      (X86_64.movq (X86_64.reg rdi) (X86_64.ind ~ofs:offset r14)) ++
      loop tail
  in
  (X86_64.label (sprintf "__new__%s__" cl.class_id)) ++
  (X86_64.pushq (X86_64.reg rbp)) ++
  (X86_64.movq (X86_64.reg rsp) (X86_64.reg rbp)) ++
  (loop (remove_arg_cons cl.class_members cl)) ++
  (X86_64.popq rbp) ++
  (X86_64.ret)
;;

let compile_method cl meth =
  let rec make_var_loc l_arg i =
    match l_arg with
    |[] -> [("this", i)]
    |head::tail ->
      if Scala_type.string_of_type head.param_ty = "Array" then
        make_var_loc tail i
      else
        (head.param_id, i)::(make_var_loc tail (i + 8))
  in
  let var_loc = make_var_loc (List.rev meth.method_param) 16 in
  let code_exp = compile_expr meth.method_body var_loc meth in
  (X86_64.label (sprintf "__%s__METHOD__%s__" cl.class_id meth.method_id)) ++
  (X86_64.pushq (X86_64.reg rbp)) ++
  (X86_64.movq (X86_64.reg rsp) (X86_64.reg rbp)) ++
  code_exp ++
  (X86_64.label (sprintf "__%s__METHOD__%s__END" cl.class_id meth.method_id)) ++
  (X86_64.movq (X86_64.reg rdi) (X86_64.reg rax)) ++
  (X86_64.popq rbp) ++
  (X86_64.ret)
;;

let compile_class cl p =
  Hashtbl.add mes_objets cl.class_id cl;
  let (my_text, my_data) = p in
  let out_data = compile_desc_class cl my_data in
  let out_text =
    my_text ++
    (compile_cons_class cl) ++
    (List.fold_left (fun x y -> x ++ (compile_method cl y)) (X86_64.nop) cl.class_methods)
  in
  (out_text, out_data)
;;

let compile_main my_main p =
  let (my_text, my_data) = p in
  let offset = find_offset_methods my_main "main" in
  let out_text =
    (X86_64.glabel "main") ++
    (X86_64.movq (X86_64.reg rsp) (X86_64.reg rbp)) ++
    (X86_64.movq (X86_64.imm ((List.length my_main.class_members + 1) * 8)) (X86_64.reg rdi)) ++
    (X86_64.call "malloc") ++
    (X86_64.movq (X86_64.reg rax) (X86_64.reg r15)) ++
    (X86_64.movq (X86_64.ilab "descr_Main") (X86_64.ind ~ofs:0 r15)) ++
    (X86_64.pushq (X86_64.reg r15)) ++
    (X86_64.call "__new__Main__") ++
    (X86_64.popq rdi) ++
    (X86_64.pushq (X86_64.reg rdi)) ++
    (X86_64.movq (X86_64.ind ~ofs:0 rdi) (X86_64.reg r13)) ++
    (X86_64.call_star (X86_64.ind ~ofs:offset r13)) ++
    (X86_64.popq rdi) ++
    (X86_64.xorq (X86_64.reg rax) (X86_64.reg rax)) ++
    (X86_64.ret) ++
    my_text
  in
  (out_text, my_data)
;;


let compile_program f output_file =
  let (my_text, my_data) = List.fold_left (fun x cl -> compile_class cl x) (X86_64.nop, X86_64.nop) (f.class_def @ [f.main]) in
  let (my_text, my_data) = compile_main f.main (my_text, my_data) in
  let my_p =
    {text =
      my_text;
     data =
       init_data () ++
       my_data;}
  in
  print_in_file output_file my_p
;;





































































