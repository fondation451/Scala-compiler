open Scala_spec;;
open Lexing;;
open Format;;

exception Typing_Error of string;;
exception Typing_Exception of string;;

let string_of_type t =
  match t with
  |TNone -> "NONE (C'est pas bien !!!)"
  |TAny -> "Any"
  |TAnyVal -> "AnyVal"
  |TBoolean -> "Boolean"
  |TInt -> "Int"
  |TUnit -> "Unit"
  |TAnyRef -> "AnyRef"
  |TString -> "String"
  |TNull -> "Null"
  |TNothing -> "Nothing"
  |TType(str, l_param) -> str
;;

let file = ref "";;

(*  Type de retour de la méthode en cours de typage
*)
let type_r = ref TNone;;

(* Classe en cours de typage *)
let cl_in_process =
  ref {class_id = "";
       class_param_type = [];
       class_param = [];
       class_extend = TNone;
       class_extend_expr = [];
       class_body = [];
       class_members = [];
       class_methods = [];
       class_loc = (Lexing.dummy_pos, Lexing.dummy_pos);}
;;

let localisation loc =
  let pos1 = fst loc in
  let pos2 = snd loc in
  let l1 = pos1.pos_lnum in
  let c1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let l2 = pos2.pos_lnum in
  let c2 = pos2.pos_cnum - pos2.pos_bol + 1 in
  sprintf "File \"%s\", line %d, characters %d-%d:\n" !file l1 c1 c2
;;

(* Renomme tout les paramètres de classe (il peuvent avoir le même nom sinon *)
(* dans le cas de classe héritée *)
let rec rename_cons_arg l_cl =
  let rec rename_cons_arg_cl cl =
    List.iter (fun x -> x.param_id <- (sprintf "**%s**consParam**%s" cl.class_id x.param_id)) cl.class_param;
  in
  List.iter rename_cons_arg_cl l_cl
;;

(*  Trouve une variable d'identifiant str dans le contexte ctx
*)
let find_var str ctx =
  let (obj, constr, l_var) = ctx in
  List.find (fun x -> x.var_id = str) l_var
;;

(*  Trouve le type de la variable d'identifiant str dans l'environnement ctx
*)
let find_type_var str ctx =
  let my_v = find_var str ctx in
  my_v.var_ty
;;

(*  Trouve une variable membre de la classe cl d'identifiant str
*)
let find_members cl str =
  let l_var = cl.class_members in
  let v = List.find (fun x -> x.var_id = str) l_var in
  v
;;

(*  Trouve le type d'un attribut d'identifiant str dans une classe cl
*)
let find_type_members cl str =
  let l_var = cl.class_members in
  let v = List.find (fun x -> x.var_id = str) l_var in
  v.var_ty
;;

(*  Trouve une méthode de la classe cl d'identifiant str
*)
let find_methods cl str =
  let l_meth = cl.class_methods in
  let meth = List.find (fun x -> x.method_id = str) l_meth in
  meth
;;

(*  Trouve la substitution du type formel id dans la liste de type effectif ty_subst
    à partir de la liste de type formel cl_param_ty
*)
let type_substitution ty_x cl_param_ty ty_subst =
  let rec find_index id l out =
    match l with
    |[] -> -1
    |h::t ->
      if h.param_ty_id = id then
        out
      else
        find_index id t (out+1)
  in
  match ty_x with
  |TType(id, _) ->
    let ind = find_index id cl_param_ty 0 in
    if ind <> -1 then
      List.nth ty_subst ind
    else
      ty_x
  |_ -> ty_x
;;

let is_type_equal t1 t2 =
  match t1, t2 with
  |TType(s1, l1), TType(s2, l2) -> s1 = s2
  |_ -> t1 = t2
;;

let rec is_sub_class t1 t2 ctx =
  let (obj, constr, l_var) = ctx in
  if is_type_equal t1 t2 then
    true
  else
    match t2 with
    |TNothing -> false
    |TBoolean |TInt |TUnit -> begin
      match t1 with
      |TNothing -> true
      |_ -> false
    end
    |TAnyVal -> begin
      match t1 with
      |TBoolean |TInt |TUnit |TNothing -> true
      |_ -> false
    end
    |TAnyRef -> begin
      match t1 with
      |TType(_, _) |TString |TNull |TNothing -> true
      |_ -> false
    end
    |TAny -> true
    |TNull -> begin
      match t1 with
      |TNothing -> true
      |_ -> false
    end
    |TString -> begin
      match t1 with
      |TNull |TNothing -> true
      |_ -> false
    end
    |TType(id2, l_tau2) -> begin
      match t1 with
      |TNull |TNothing -> true
      |TType(id1, l_tau1) ->
        let cl = ObjSet.find id1 obj in
        is_sub_class cl.class_extend t2 ctx
      |_ -> false
    end
    |_ -> false
;;

let rec is_sub_type t1 t2 ctx =
  let (obj, constr, l_var) = ctx in
  if t1 = t2 then
    true
  else
    match t1 with
    |TNothing -> true
    |TNull -> is_sub_class t1 t2 ctx
    |TType(c1, l_tau1) -> begin
      match t2 with
      |TType(c2, l_tau2) -> begin
        try
        if c1 = c2 then
          let cl = ObjSet.find c1 obj in
          let l_T = cl.class_param_type in
          let rec check_l_tau l_T l_tau1 l_tau2 =
            match l_T, l_tau1, l_tau2 with
            |[], [], [] -> true
            |hd1::tl1, hd2::tl2, hd3::tl3 ->
              if hd1.param_ty_variancy = [] && hd2 = hd3 then
                check_l_tau tl1 tl2 tl3
              else if List.hd hd1.param_ty_variancy = Sc_Plus_Constr && is_sub_type hd2 hd3 ctx then
                check_l_tau tl1 tl2 tl3
              else if List.hd hd1.param_ty_variancy = Sc_Sub_Constr && is_sub_type hd3 hd2 ctx then
                check_l_tau tl1 tl2 tl3
              else
                false
            |_ -> raise (Typing_Exception("Fonction is_sub_type : type du contexte et types fournis non cohérents !"))
          in
          check_l_tau l_T l_tau1 l_tau2
        else
          let cl = ObjSet.find c1 obj in
          if is_sub_class t1 t2 ctx then
            (is_sub_class (cl.class_extend) t2 ctx) && (is_sub_type cl.class_extend t2 ctx)
          else
            let (c2_constr, tau) = ObjConstr.find c2 constr in
            c2_constr = Sc_Upper_Constr && is_sub_type t1 tau ctx
        with Not_found -> false
      end
      |_ ->
        let cl = ObjSet.find c1 obj in
        (is_sub_class (cl.class_extend) t2 ctx) && (is_sub_type cl.class_extend t2 ctx)
    end
    |_ -> begin
      if is_sub_class t1 t2 ctx then
        true
      else
        match t2 with
        |TType(c2, l_tau2) ->
          let (c2_constr, tau) = ObjConstr.find c2 constr in
          c2_constr = Sc_Upper_Constr && is_sub_type t1 tau ctx
        |_ -> false 
    end
;;

(* Détermination du caractère bien fondé d'une substitution *)
let rec is_correct_subs l_T l_tau ctx =
  match l_T, l_tau with
  |[], [] -> true
  |h1::t1, h2::t2 -> begin
    match h1.param_ty_constr, h1.param_ty_ty with
    |[], [] -> is_correct_subs t1 t2 ctx
    |[Sc_Lower_Constr], [t_borne] -> (is_sub_type h2 t_borne ctx) && (is_correct_subs t1 t2 ctx)
    |[Sc_Upper_Constr], [t_borne] -> (is_sub_type t_borne h2 ctx) && (is_correct_subs t1 t2 ctx)
    |_ -> false
  end
  |_ -> false
;;

(* Détermination du caractère bien fondé d'un type *)
let rec is_correct_type t ctx =
  let (obj, constr, l_var) = ctx in
  match t with
  |TType(id, l_param) -> begin
    try
    if id = "Array" then
      true
    else
      let cl = ObjSet.find id obj in
      if List.for_all (fun x -> is_correct_type x ctx) l_param then
        is_correct_subs (cl.class_param_type) l_param ctx
      else
        false
    with Not_found -> false (*raise (Typing_Error("Type " ^ id ^ " inexistant !"))*)
  end
  |_ -> true
;;

(* Verifie l'unicité des noms *)
let rec check_name l =
  match l with
  |[] -> true
  |h::t -> (List.for_all (fun x -> x <> h) t) && (check_name t)
;;

let rec check_name_var id l =
  match l with
  |[] -> true
  |h::t ->
    if h = "" then
      true
    else
      (id <> h) && (check_name_var id t)
;;

(* Dis si une fonction a été déjà définie d'une super classe *)
let rec is_herited cl meth_id ctx =
  let (obj, constr, l_var) = ctx in
  if List.exists (fun x -> x.method_id = meth_id) cl.class_methods then
    true
  else
    match cl.class_extend with
    |TType(cl_ext_id, arg_ty) ->
      let cl_ext = ObjSet.find cl_ext_id obj in
      is_herited cl_ext meth_id ctx
    |_ -> false
;;

let substitute l_T1_s l_T2_s x_ty =
  let rec loop l_T1 l_T2 x_ty =
    match l_T1, l_T2 with
    |[], [] -> begin
      match x_ty with
      |TType(x_ty_id, x_l_arg) -> TType(x_ty_id, List.map (fun x -> loop l_T1_s l_T2_s x) x_l_arg)
      |_ -> x_ty
    end
    |h1::t1, h2::t2 -> begin
      match x_ty with
      |TType(x_ty_id, x_l_arg) ->
        if h1 = x_ty_id then
          h2
        else
          loop t1 t2 x_ty
      |_ -> x_ty
    end
  in
  loop l_T1_s l_T2_s x_ty
;;

let rec substitute_l_var l_T1 l_T2 l_var =
  match l_var with
  |[] -> []
  |h::t -> {var_id = h.var_id; var_ty = substitute l_T1 l_T2 h.var_ty;
            var_v = h.var_v; var_mut = h.var_mut;}::(substitute_l_var l_T1 l_T2 t)
;;

let rec substitute_l_meth l_T1 l_T2 l_meth =
  match l_meth with
  |[] -> []
  |h::t ->
    {method_id = h.method_id;
     method_param_type = h.method_param_type;
     method_param =
       List.map (fun x -> {param_id = x.param_id; param_ty = substitute l_T1 l_T2 x.param_ty}) h.method_param;
     method_out_ty = substitute l_T1 l_T2 h.method_out_ty;
     method_body = h.method_body;
     method_override = h.method_override;
     method_obj = h.method_obj;
     method_loc = h.method_loc;}::(substitute_l_meth l_T1 l_T2 t)
;;

let get_type_id t =
  match t with
  |TType(id, _) -> id
  |_ -> ""
;;

let get_variance m_T cl =
  let tmp = List.find (fun x -> x.param_ty_id = m_T) cl.class_param_type in
  match tmp.param_ty_variancy with
  |[] -> Sc_Neutre_Constr
  |_ -> List.hd tmp.param_ty_variancy
;;

let is_cl_param_ty m_t cl =
  match m_t with
  |TType(id, _) ->
    List.exists (fun x -> x.param_ty_id = id) cl.class_param_type
  |_ -> false
;;

let rec check_variance_positive x_ty cl ctx =
  let (obj, constr, l_var) = ctx in
  match x_ty with
  |TType(id, arg_ty) ->
    if List.exists (fun x -> x.param_ty_id = id) cl.class_param_type then
      let variance = get_variance id cl in
      variance <> Sc_Sub_Constr
    else
      let id_cl = ObjSet.find id obj in
      List.for_all2
        (fun x y ->
          if y.param_ty_variancy <> [] then
            match List.hd y.param_ty_variancy with
            |Sc_Plus_Constr -> check_variance_positive x cl ctx
            |Sc_Sub_Constr -> check_variance_negative x cl ctx
            |Sc_Neutre_Constr -> true
          else
            (check_variance_positive x cl ctx) && (check_variance_negative x cl ctx))
        arg_ty id_cl.class_param_type
  |_ -> true

and check_variance_negative x_ty cl ctx =
  let (obj, constr, l_var) = ctx in
  match x_ty with
  |TType(id, arg_ty) ->
    if List.exists (fun x -> x.param_ty_id = id) cl.class_param_type then
      let variance = get_variance id cl in
      variance <> Sc_Plus_Constr
    else
      let id_cl = ObjSet.find id obj in
      List.for_all2
        (fun x y ->
          if y.param_ty_variancy <> [] then
            match List.hd y.param_ty_variancy with
            |Sc_Plus_Constr -> check_variance_negative x cl ctx
            |Sc_Sub_Constr -> check_variance_positive x cl ctx
            |Sc_Neutre_Constr -> true
          else
            (check_variance_positive x cl ctx) && (check_variance_negative x cl ctx))
        arg_ty id_cl.class_param_type
  |_ -> true
;;

(* Type une expression e dans le contexte ctx
*)
let rec type_expr e_dec ctx =
  let (obj, constr, l_var) = ctx in
  let e = e_dec.desc in
  let loc = e_dec.loc in
  match e with
  |EInteger(i) ->
    {desc = e; loc = loc; e_ty = TInt;}
  |EString(str) ->
    {desc = e; loc = loc; e_ty = TString;}
  |EBool(b) ->
    {desc = e; loc = loc; e_ty = TBoolean;}
  |ENull ->
    {desc = e; loc = loc; e_ty = TNull;}
  |EThis ->
    let t = find_type_var "this" ctx in
    {desc = e; loc = loc; e_ty = t;}
  |EUnit ->
    {desc = e; loc = loc; e_ty = TUnit;}
  |EAccess(a) -> begin
    match a with
    |Access_Ident(str) -> begin
      try
      let t = find_type_var str ctx in
      {desc = e; loc = loc; e_ty = t;}
      with Not_found ->
        type_expr {desc = (EAccess(Access_Point({desc = EThis; loc = e_dec.loc; e_ty = TNone}, str))); loc = e_dec.loc; e_ty = TNone} ctx
    end
    |Access_Point(exp, str) -> begin
      let new_exp = type_expr exp ctx in
      match new_exp.e_ty with
      |TType(cl_id, l_subst) -> begin
        try
        let cl = ObjSet.find cl_id obj in
        let new_str =
          if List.exists (fun x -> x.param_id = (sprintf "**%s**consParam**%s" cl.class_id str)) cl.class_param then
            (sprintf "**%s**consParam**%s" cl.class_id str)
          else
            str
        in
        let ty_x_id = find_type_members cl new_str in
        let ty_out = type_substitution ty_x_id cl.class_param_type l_subst in
        {desc = EAccess(Access_Point(new_exp, new_str)); loc = loc; e_ty = ty_out;}
        with Not_found -> raise (Typing_Error((localisation loc) ^ "Variable membre inexistante !"))
      end
      |_ -> raise (Typing_Exception("Un type de base n'a pas d'attributs !"))
    end
  end
  |EAffectation(a, exp) -> begin
    let new_exp = type_expr exp ctx in
    match a with
    |Access_Ident(str) -> begin
      try
      let v = find_var str ctx in
      if v.var_mut then
        if is_sub_type new_exp.e_ty v.var_ty ctx then
          {desc = EAffectation(a, new_exp); loc = loc; e_ty = TUnit;}
        else
          raise (Typing_Error((localisation loc) ^ (sprintf "%s n'est pas un sous type de %s !" (string_of_type new_exp.e_ty) (string_of_type v.var_ty))))
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Variable %s non mutable !" v.var_id)))
      with Not_found -> type_expr {desc = (EAffectation(Access_Point({desc = EThis; loc = e_dec.loc; e_ty = TNone}, str), exp)); loc = e_dec.loc; e_ty = TNone} ctx
    end
    |Access_Point(left_exp, str) -> begin
      let new_left_exp = type_expr left_exp ctx in
      match new_left_exp.e_ty with
      |TType(cl_id, l_subst) -> begin
        try
        let cl = ObjSet.find cl_id obj in
        let v = find_members cl str in
        let ty_out = type_substitution v.var_ty cl.class_param_type l_subst in
        if v.var_mut then
          if is_sub_type new_exp.e_ty ty_out ctx then
            {desc = EAffectation(Access_Point(new_left_exp, str), new_exp); loc = loc; e_ty = TUnit;}
          else
            raise (Typing_Error((localisation loc) ^ (sprintf "%s n'est pas un sous type de %s !" (string_of_type new_exp.e_ty) (string_of_type ty_out))))
        else
          raise (Typing_Error((localisation loc) ^ (sprintf "Variable %s non mutable !" v.var_id)))
        with Not_found -> raise (Typing_Error((localisation loc) ^ (sprintf "Variable membre %s de l'objet %s inexistante !" str cl_id)))
      end
      |_ -> raise (Typing_Exception("Un type de base n'a pas d'attributs !"))
    end
  end
  |ECall(a_exp, a_id, arg_ty, l_exp) -> begin
    let new_a_exp = type_expr a_exp ctx in
    match new_a_exp.e_ty with
    |TType(cl_id, l_subst) -> begin
      let rec check_type_param l_tau l_exp =
        match l_tau, l_exp with
        |[], [] -> []
        |h1::t1, h2::t2 ->
          let new_e = type_expr h2 ctx in
          if is_sub_type new_e.e_ty h1 ctx then
            new_e::(check_type_param t1 t2)
          else
            raise (Typing_Error((localisation loc) ^ (sprintf "%s n'est pas un sous type de %s !" (string_of_type new_e.e_ty) (string_of_type h1))))
        |_ -> raise (Typing_Error((localisation loc) ^ (sprintf "Objet : %s Méthode : %s, nombre d'arguments fournis incorrect !" cl_id a_id)))
      in
      try
      let cl = ObjSet.find cl_id obj in
      let meths = find_methods cl a_id in
      if List.for_all (fun x -> is_correct_type x ctx) arg_ty then
        let l_str_meth_param_type = List.map (fun x -> x.param_ty_id) meths.method_param_type in
        let l_str_cl_param_type = List.map (fun x -> x.param_ty_id) cl.class_param_type in
        
        (* On crée la substitution sigma o sigma' avec les contraintes pour vérifier le caractère bien fondé *)
        let method_param_type_subs =
          List.map
            (fun x -> {param_ty_variancy = x.param_ty_variancy;
                       param_ty_id =
                         (let ty_sub = substitute l_str_cl_param_type
                                                  l_subst
                                                  (substitute l_str_meth_param_type 
                                                              arg_ty 
                                                              (TType(x.param_ty_id, [])))
                         in
                         string_of_type ty_sub);
                       param_ty_constr = x.param_ty_constr;
                       param_ty_ty =
                         if x.param_ty_ty = [] then
                           []
                         else
                           [substitute l_str_cl_param_type
                                       l_subst
                                       (substitute l_str_meth_param_type
                                                   arg_ty
                                                   (List.hd x.param_ty_ty))];}) meths.method_param_type
        in
        if is_correct_subs method_param_type_subs arg_ty ctx then
          (* Substitution des paramètres formels de la fonction *)
          let param_type_sub =
            List.map (fun x -> substitute l_str_cl_param_type
                                          l_subst
                                          (substitute l_str_meth_param_type
                                                      arg_ty
                                                      x.param_ty)) meths.method_param
          in
          let new_l_exp = check_type_param param_type_sub l_exp in
          let t_out = substitute l_str_meth_param_type
                     arg_ty
                     (substitute l_str_cl_param_type
                                 l_subst
                                 meths.method_out_ty) in
          {desc = ECall(new_a_exp, a_id, arg_ty, new_l_exp); loc = loc; e_ty = t_out;}
        else
          raise (Typing_Error((localisation loc) ^ (sprintf "Les types des arguments de la méthode %s de l'objet %s ne sont pas bien fondés !" cl_id a_id)))
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Les arguments de types de la méthode %s de l'objet %s ne sont pas bien fondés !" cl_id a_id)))
      with Not_found -> raise (Typing_Error((localisation loc) ^ (sprintf "Objet %s ou méthode %s inexistante !" cl_id a_id)))
    end
    |_ -> (*TUnit*) raise (Typing_Error((localisation loc) ^ "Appel de méthode sur un type de base"))
  end
  |EInstanciation(str, arg_ty, l_exp) ->
    let rec check_type_param l_sub l_exp =
      match l_sub, l_exp with
      |[], [] -> []
      |h1::t1, h2::t2 ->
        let new_e = type_expr h2 ctx in
        if is_sub_type new_e.e_ty h1 ctx then
          new_e::(check_type_param t1 t2)
        else
          raise (Typing_Error((localisation loc) ^ (sprintf "%s n'est pas un sous type de %s !" (string_of_type new_e.e_ty) (string_of_type h1))))
      |_ -> raise (Typing_Error((localisation loc) ^ (sprintf "Appel du constructeur de l'objet %S avec un nombre invalide d'arguments !" str)))
    in
    let ty_out = TType(str, arg_ty) in
    if is_correct_type ty_out ctx then
      let cl = ObjSet.find str obj in
      let l_str_cl_param_type = List.map (fun x -> x.param_ty_id) cl.class_param_type in
      let param_type_sub = List.map (fun x -> substitute l_str_cl_param_type arg_ty x.param_ty) cl.class_param in
      let new_l_exp = check_type_param param_type_sub l_exp in
      {desc = EInstanciation(str, arg_ty, new_l_exp); loc = loc; e_ty = ty_out;}
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "Le type %s de l'instanciation n'est pas bien fondé !" str)))
  |ENot(exp) ->
    let new_exp = type_expr exp ctx in
    if new_exp.e_ty = TBoolean then
      {desc = ENot(new_exp); loc = loc; e_ty = new_exp.e_ty;}
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "Operateur Not : on attendait un booléen mais on a reçu un %s !" (string_of_type new_exp.e_ty))))
  |ENeg(exp) ->
    let new_exp = type_expr exp ctx in
    if new_exp.e_ty = TInt then
      {desc = ENeg(new_exp); loc = loc; e_ty = new_exp.e_ty;}
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "Operateur de négation : on attendait un entier mais on a reçu un %s !"(string_of_type new_exp.e_ty))))
  |EOp(exp1, op, exp2) -> begin
    let new_exp1 = type_expr exp1 ctx in
    let new_exp2 = type_expr exp2 ctx in
    match op with
    |Op_Eq |Op_Ne ->
      if (is_sub_type new_exp1.e_ty TAnyRef ctx) && (is_sub_type new_exp2.e_ty TAnyRef ctx) then
        {desc = EOp(new_exp1, op, new_exp2); loc = loc; e_ty = TBoolean;}
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Operateur Eq ou Ne : %s n'est pas un sous type de %s ou %s n'est pas un sous type de %s !" (string_of_type new_exp1.e_ty) (string_of_type TAnyRef) (string_of_type new_exp2.e_ty) (string_of_type TAnyRef))))
    |Op_Physical_Eq |Op_Physical_Ne |Op_Less |Op_Less_Eq |Op_Greater |Op_Greater_Eq ->
      if new_exp1.e_ty = TInt && new_exp2.e_ty = TInt then
        {desc = EOp(new_exp1, op, new_exp2); loc = loc; e_ty = TBoolean;}
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Operateur de comparaison : %s ou %s n'est pas un Int !" (string_of_type new_exp1.e_ty) (string_of_type new_exp2.e_ty))))
    |Op_Add |Op_Sub |Op_Mul |Op_Div |Op_Mod ->
      if new_exp1.e_ty = TInt && new_exp2.e_ty = TInt then
        {desc = EOp(new_exp1, op, new_exp2); loc = loc; e_ty = TInt;}
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Operateur arithmétique : %s ou %s n'est pas un Int !" (string_of_type new_exp1.e_ty) (string_of_type new_exp2.e_ty))))
    |Op_And |Op_Or ->
      if new_exp1.e_ty = TBoolean && new_exp2.e_ty = TBoolean then
        {desc = EOp(new_exp1, op, new_exp2); loc = loc; e_ty = TBoolean;}
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "Operateur logique :  %s ou %s n'est pas un Bool !" (string_of_type new_exp1.e_ty) (string_of_type new_exp2.e_ty))))
  end
  |EIfThenElse(exp1, exp2, exp3) -> begin
    let new_exp1 = type_expr exp1 ctx in
    let new_exp2 = type_expr exp2 ctx in
    let new_exp3 = type_expr exp3 ctx in
    if new_exp1.e_ty = TBoolean then
      if is_sub_type new_exp2.e_ty new_exp3.e_ty ctx then
        {desc = EIfThenElse(new_exp1, new_exp2, new_exp3); loc = loc; e_ty = new_exp3.e_ty;}
      else if is_sub_type new_exp3.e_ty new_exp2.e_ty ctx then
        {desc = EIfThenElse(new_exp1, new_exp2, new_exp3); loc = loc; e_ty = new_exp2.e_ty;}
      else
        raise (Typing_Error((localisation loc) ^ (sprintf "If : type de la branche THEN : %s incompatible avec le type de la branche ELSE : %s !" (string_of_type new_exp2.e_ty) (string_of_type new_exp3.e_ty))))
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "If : Condition de type %s != Bool !" (string_of_type new_exp1.e_ty))))
  end
  |EWhile(exp1, exp2) -> begin
    let new_exp1 = type_expr exp1 ctx in
    let new_exp2 = type_expr exp2 ctx in
    if new_exp1.e_ty = TBoolean then
      {desc = EWhile(new_exp1, new_exp2); loc = loc; e_ty = TUnit;}
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "While : Condition de type %s != Bool !" (string_of_type new_exp1.e_ty))))
  end
  |EReturn(exp) -> begin
    let new_exp = type_expr exp ctx in
    if !type_r = TNone then
      raise (Typing_Error((localisation loc) ^ (sprintf "Return en dehors d'une méthode !")))
    else if is_sub_type new_exp.e_ty !type_r ctx then
      {desc = EReturn(new_exp); loc = loc; e_ty = TNothing;}
    else
      raise (Typing_Error((localisation loc) ^ (sprintf "Return : %s n'est pas un sous type de %s !" (string_of_type new_exp.e_ty) (string_of_type !type_r))))
  end
  |Eprint(exp) -> begin
    let new_exp = type_expr exp ctx in
    match new_exp.e_ty with
    |TInt |TString ->
      {desc = Eprint(new_exp); loc = loc; e_ty = TUnit;}
    |_ -> raise (Typing_Error((localisation loc) ^ (sprintf "Operateur Print : type de l'argument invalide : %s !" (string_of_type new_exp.e_ty))))
  end
  |EBlock(l_b) -> begin
    let rec type_block l_b ctx =
      let (obj, constr, l_var) = ctx in
      match l_b with
      |[] -> ([], TUnit)
      |[h] -> begin
        match h with
        |Block_Var(v) ->
          type_block [h ; Block_Expr({desc = EUnit; loc = e_dec.loc; e_ty = TNone})] ctx
        |Block_Expr(exp) ->
          let new_exp = type_expr exp ctx in
          ([Block_Expr(new_exp)], new_exp.e_ty)
      end
      |h::tail -> begin
        match h with
        |Block_Var(v) -> begin
          if not (check_name_var v.var_id (List.map (fun x -> x.var_id) l_var)) then
            raise (Typing_Error((localisation loc) ^ (sprintf "Il existe déjà une variable appelé %s dans ce bloc !" v.var_id)));
          
          let new_exp_v = type_expr v.var_v ctx in
          if v.var_ty = TNone then
           (v.var_ty <- new_exp_v.e_ty;
            v.var_v <- new_exp_v;
            let (new_l_b, out) = type_block tail (obj, constr, v::l_var) in
            (Block_Var(v)::new_l_b, out))
          else if is_correct_type v.var_ty ctx && is_sub_type new_exp_v.e_ty v.var_ty ctx then
           (v.var_v <- new_exp_v;
            let (new_l_b, out) = type_block tail (obj, constr, v::l_var) in
            (Block_Var(v)::new_l_b, out))
          else
            raise (Typing_Error((localisation loc) ^ (sprintf "Création de variable dans un bloc : le type %s n'est pas bien fondé ou bien %s n'est pas un sous type de %s !" (string_of_type v.var_ty) (string_of_type new_exp_v.e_ty) (string_of_type v.var_ty))))
        end
        |Block_Expr(exp) ->
          let new_exp = type_expr exp ctx in
          let (new_l_b, out) = type_block tail ctx in
          (Block_Expr(new_exp)::new_l_b, out)
      end
    in
    let (new_b, out) = type_block l_b (obj, constr, {var_id = ""; var_ty = TNone; var_v = {desc = EUnit; loc = e_dec.loc; e_ty = TNone}; var_mut= false;}::l_var) in
    {desc = EBlock(new_b); loc = loc; e_ty = out;}
  end
;;


let rec check_param_type l ctx =
  let (obj, constr, l_var) = ctx in
  match l with
  |[] -> ctx
  |h::t -> begin
    if h.param_ty_ty <> [] && not (is_correct_type (List.hd h.param_ty_ty) ctx) then
      raise (Typing_Error("Contrainte de type : le type de la contrainte n'est pas bien fondé !"));
    let new_cl =
      {class_id = h.param_ty_id;
       class_param_type = [];
       class_param = [];
       class_extend =
         if h.param_ty_constr <> [] && List.hd h.param_ty_constr = Sc_Lower_Constr then
           List.hd h.param_ty_ty
         else
           TAnyRef;
       class_extend_expr = [];
       class_body = [];
       class_members = [];
       class_methods = [];
       class_loc = (Lexing.dummy_pos, Lexing.dummy_pos);
      }
    in
    let new_constr =
      if h.param_ty_constr <> [] && List.hd h.param_ty_constr = Sc_Upper_Constr then
        ObjConstr.add new_cl.class_id (Sc_Upper_Constr, List.hd h.param_ty_ty) constr
      else if h.param_ty_constr <> [] && List.hd h.param_ty_constr = Sc_Lower_Constr then
        ObjConstr.add new_cl.class_id (Sc_Lower_Constr, List.hd h.param_ty_ty) constr
      else
        constr
    in
    (*let new_obj = ObjSet.add new_cl.class_id new_cl obj in*)
    let (obj, constr, l_var) = type_class new_cl (obj, new_constr, l_var) in
    check_param_type t (obj, constr, l_var)
  end

and check_param_type_arg l ctx =
  let (obj, constr, l_var) = ctx in
  match l with
  |[] -> ctx
  |hd::tl ->
    if is_correct_type hd.param_ty ctx then
      check_param_type_arg tl (obj, constr,
                          {var_id = hd.param_id;
                           var_ty = hd.param_ty;
                           var_v  = {desc = EUnit; loc = (Lexing.dummy_pos, Lexing.dummy_pos); e_ty = TNone};
                           var_mut = false;}::l_var)
    else
      raise (Typing_Error("Les type du constructeur ne sont pas bien fondés !"));

and check_param_type_arg_class l cl ctx =
  match l with
  |[] -> ctx
  |hd::tl ->
    if is_correct_type hd.param_ty ctx then
      (cl.class_members <- ({var_id = hd.param_id;
                            var_ty = hd.param_ty;
                            var_v  = {desc = EUnit; loc = (Lexing.dummy_pos, Lexing.dummy_pos); e_ty = TNone};
                            var_mut = false;}::cl.class_members);
      check_param_type_arg_class tl cl ctx)
    else
      raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Les type du constructeur de la classe %s ne sont pas bien fondés !" cl.class_id)));

and check_methods cl meth ctx =
  let l_T = meth.method_param_type in
  let ctx = check_param_type l_T ctx in
  
  let ctx = check_param_type_arg meth.method_param ctx in
  
(*  cl.class_methods <- meth::cl.class_methods;*)
  
  (* Vérification de la variance des contraintes de types d'une méthode *)
  if not (List.for_all
           (fun x -> 
             if x.param_ty_constr <> [] then
               match List.hd x.param_ty_constr with
               |Sc_Lower_Constr -> check_variance_negative (List.hd x.param_ty_ty) cl ctx
               |Sc_Upper_Constr -> check_variance_positive (List.hd x.param_ty_ty) cl ctx
             else
               true) meth.method_param_type) then
    raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Problème de variance avec les contraintes de types de la méthode %s de l'objet %s !" meth.method_id cl.class_id)));
  
  (* Vérification de la variance des types des arguments d'une méthode *)
  if meth.method_id <> "main" && not (List.for_all (fun x -> check_variance_negative x.param_ty cl ctx) meth.method_param) then
    raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Problème de variance avec les types des arguments de la méthode %s de l'objet %s !" meth.method_id cl.class_id)));
  
  (* Vérification de la variance du type de retour d'une méthode *)
  if not (check_variance_positive meth.method_out_ty cl ctx) then
    raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Problème de variance avec le type de retour de la méthode %s de l'objet %s !" meth.method_id cl.class_id)));
  
  let new_body = type_expr meth.method_body ctx in
  meth.method_body <- new_body;
  if not (is_sub_type new_body.e_ty meth.method_out_ty ctx) then
    raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Méthode %s de l'objet %s : %s (type du corps de la méthode) n'est pas un sous type de %s (type de retour attendu) !" meth.method_id cl.class_id (string_of_type new_body.e_ty) (string_of_type meth.method_out_ty))));


and type_class cl ctx =
  let (obj, constr, l_var) = ctx in
  
  cl_in_process := cl;
  
  (* Vérification de l'unicité des noms de paramètres de types ! *)
  if not (check_name (List.rev_map (fun x -> x.param_ty_id) cl.class_param_type)) then
    raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Des paramètres de types de la classe %s ont le même nom !" cl.class_id)));
  
  (* Vérification de l'unicité des noms des paramètres du constructeur *)
  if not (check_name (List.rev_map (fun x -> x.param_id) cl.class_param)) then
    raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Des paramètres du constructeur de la classe %s ont le même nom !" cl.class_id)));
  
  (* Partie 1 *)
  let l_T = cl.class_param_type in
  let (obj, constr, l_var) = check_param_type l_T (obj, constr, l_var) in
  
  (* Partie 2 *)  (* Héritage de la classe mère *)
  let (obj, constr, l_var) =
   (match cl.class_extend with
    |TType(cl_ext_id, cl_ext_param) -> begin
      if is_correct_type cl.class_extend (obj, constr, l_var) then
        try
        let cl_ext = ObjSet.find cl_ext_id obj in
        
        let l_members =
          substitute_l_var (List.map (fun x -> x.param_ty_id) cl_ext.class_param_type )
                           cl_ext_param
                           (List.rev cl_ext.class_members)
        in
        
        let rec include_param_herite l_m l_p l_e =
          match l_m with
          |[] -> []
          |head::tail ->
            if List.exists (fun x -> head.var_id = x.param_id) l_p then
              (head.var_v <- (List.hd l_e);
              cl.class_body <- (Decl_Var(head))::(cl.class_body);
              (include_param_herite tail l_p (List.tl l_e)))
            else
              head::(include_param_herite tail l_p l_e)
        in
        
        cl.class_members <- include_param_herite l_members cl_ext.class_param (List.rev cl.class_extend_expr);
        cl.class_methods <- 
          substitute_l_meth (List.map (fun x -> x.param_ty_id) cl_ext.class_param_type )
                            cl_ext_param
                            (List.rev cl_ext.class_methods);
        let new_obj = ObjSet.add cl.class_id cl obj in
        (new_obj, constr, l_var)
        with Not_found -> raise (Typing_Error("Classe mère inexistante !"));
      else
        raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Le type de la classe mère : %s de l'objet %s n'est pas bien fondé !" (string_of_type cl.class_extend) cl.class_id)))
    end
    |_ -> begin
      let new_obj = ObjSet.add cl.class_id cl obj in
      (new_obj, constr, l_var)
    end)
  in

  (* Partie 3 *)  (* Inclusion du this et des paramètres de type dans l'environnement *)
  let rec create_param_type_list l =
    match l with
    |[] -> []
    |hd::tl ->
      (TType(hd.param_ty_id, []))::(create_param_type_list tl)
  in
  
  let (obj, constr, l_var) = check_param_type_arg_class cl.class_param cl (obj, constr, l_var) in
  let (obj, constr, l_var) = (obj, constr,
                              {var_id = "this";
                               var_ty = TType(cl.class_id, create_param_type_list cl.class_param_type);
                               var_v  = {desc = EUnit; loc = (Lexing.dummy_pos, Lexing.dummy_pos); e_ty = TNone};
                               var_mut = false;}::l_var)
  in
  (* Partie 4 *)
  (match cl.class_extend with
    |TAnyRef -> ()
    |TType(cl_ext_id, cl_ext_param) ->
      type_expr {desc = EInstanciation(cl_ext_id, cl_ext_param, cl.class_extend_expr); loc = (Lexing.dummy_pos, Lexing.dummy_pos); e_ty = TNone} (obj, constr, l_var);
      ()
    |_ -> ());
  
  (* Vérification de la variance de l'extend *)
  if not (check_variance_positive cl.class_extend cl (obj, constr, l_var)) then
    raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Problème de variance avec l'extend de la classe %s !" cl.class_id)));
  
  (* Vérification de la variance des contraintes de types d'une classe *)
  if not (List.for_all
           (fun x -> 
             if x.param_ty_constr <> [] then
               match List.hd x.param_ty_constr with
               |Sc_Lower_Constr -> check_variance_positive (List.hd x.param_ty_ty) cl (obj, constr, l_var)
               |Sc_Upper_Constr -> check_variance_negative (List.hd x.param_ty_ty) cl (obj, constr, l_var)
             else
               true) cl.class_param_type) then
    raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Problème de variance avec les contraintes de types de la classe %s !" cl.class_id)));

  (* Partie 5 : vérification des différentes déclarations *)
  let rec check_decl l ctx =
    let (obj, constr, l_var) = ctx in
    match l with
    |[] -> ctx
    |hd::tl -> begin
      match hd with
      |Decl_Var(var) ->
        (* Vérification de la variance d'un champs de classe *)
        if var.var_mut = false && not (check_variance_positive var.var_ty cl ctx) then
          raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Problème de variance avec un champs non mutable %s de la classe %s !" var.var_id cl.class_id)))
        else if var.var_mut && (not (check_variance_positive var.var_ty cl ctx) || not (check_variance_negative var.var_ty cl ctx)) then
          raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Problème de variance avec un champs mutable %s de la classe %s !" var.var_id cl.class_id)));
        
        let new_exp_v = type_expr var.var_v ctx in
        if var.var_ty = TNone then
         (var.var_ty <- new_exp_v.e_ty;
          var.var_v <- new_exp_v;
          cl.class_members <- var::cl.class_members;
          check_decl tl ctx)
        else if is_correct_type var.var_ty ctx && is_sub_type new_exp_v.e_ty var.var_ty ctx then
         (var.var_v <- new_exp_v;
          cl.class_members <- var::cl.class_members;
          check_decl tl ctx)
        else
          raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Objet %s, création d'une variable membre : type incompatible : %s n'est pas un sous type de %s !" cl.class_id (string_of_type new_exp_v.e_ty) (string_of_type var.var_ty))))
      |Decl_Meth(meth) ->
        if not (check_name (List.rev_map (fun x -> x.param_ty_id) meth.method_param_type)) then
          raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Des paramètres de types de la méthode %s de l'objet %s ont le même nom !" meth.method_id cl.class_id)));
        if not (check_name (List.rev_map (fun x -> x.param_id) meth.method_param)) then
          raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Des paramètres de la méthode %s de l'objet %s ont le même nom !" meth.method_id cl.class_id)));
        
        meth.method_obj <- cl.class_id;
        
        (* Vérification que l'override est placé correctement *)
        (* Si la méthode hérite, on retire la méthode mère de la classe *)
        (match cl.class_extend with
        |TType(cl_ext_id, cl_ext_param) ->
          let rec remove_parent_method my_meth l_meth =
            match l_meth with
            |[] -> []
            |h::t ->
              if h.method_id = my_meth.method_id then
                my_meth::t
              else
                h::(remove_parent_method my_meth t)
          in          
          let cl_ext = ObjSet.find cl_ext_id obj in
          let is_heri = is_herited cl_ext meth.method_id ctx in
          if is_heri && meth.method_override = false then
            raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "La méthode %s est héritée mais ne possède pas d'override !" meth.method_id)))
          else if not (is_heri) && meth.method_override then
            raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "La méthode %s n'est pas héritée mais possède un override !" meth.method_id)))
          else if is_heri then
            try
            let meth_parent = List.find (fun x -> x.method_id = meth.method_id) cl.class_methods in
            
            (* Alpha équivalence *)
            let l_alpha = List.mapi (fun i x -> TType(" ALPHA" ^ (string_of_int i), [])) meth.method_param_type in
            let l_T = List.map (fun x -> x.param_ty_id) meth.method_param_type in
            let l_T_ext = List.map (fun x -> x.param_ty_id) meth_parent.method_param_type in
            let out_ty_alph = substitute l_T l_alpha meth.method_out_ty in
            let out_ty_alph_ext = substitute l_T_ext l_alpha meth_parent.method_out_ty in
            
            let param_ty_alph = List.map (fun x -> substitute l_T l_alpha x.param_ty) meth.method_param in
            let param_ty_alph_ext =
              List.map (fun x -> substitute l_T_ext l_alpha x.param_ty) meth_parent.method_param
            in
            
            if not (is_sub_type out_ty_alph out_ty_alph_ext ctx) ||
               not (List.for_all2
                     (fun x y -> x = y) param_ty_alph param_ty_alph_ext) then
              raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "La méthode %s n'a pas les mêmes types que sa méthode mère !" meth.method_id)));
            cl.class_methods <- remove_parent_method meth cl.class_methods
            with Invalid_argument(_) -> raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "La méthode %s n'a pas le même nombre d'arguments que sa méthode mère !" meth.method_id)))
          else
            cl.class_methods <- meth::cl.class_methods
        |_ ->
          if meth.method_override then
            raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "La méthode %s n'est pas héritée mais possède un override !" meth.method_id)))
          else
            cl.class_methods <- meth::cl.class_methods);
        
        if not (check_name (List.rev_map (fun x -> x.method_id) cl.class_methods)) then
          raise (Typing_Error((localisation meth.method_loc) ^ (sprintf "Il existe déjà une méthode appelé %s !" meth.method_id)));
        
        type_r := meth.method_out_ty;
        check_methods cl meth ctx;
        type_r := TNone;
        check_decl tl ctx
    end
  in
  (* On vérifie toutes les déclarations *)
  check_decl cl.class_body (obj, constr, l_var);
  
  (* On remet les membres et les méthodes dans le bon ordre *)
  
  cl.class_members <- List.rev cl.class_members;
  cl.class_members <-
  (match cl.class_extend with
    |TType(cl_ext_id, cl_ext_param) ->
      let cl_ext = ObjSet.find cl_ext_id obj in
      let rec loop l_m_ext l =
        match l_m_ext with
        |[] -> l
        |head::tail ->
          let tmp = List.find (fun x -> x.var_id = head.var_id) l in
          let new_l = List.filter (fun x -> x.var_id <> head.var_id) l in
          tmp::(loop tail new_l)
      in
      loop cl_ext.class_members cl.class_members
    |_ -> cl.class_members);
  
  cl.class_methods <- List.rev cl.class_methods;
  
  (* On récupère le contexte initiale et on lui ajoute la classe nouvellement créé *)
  (* Les classes représentant les paramètres de type ne sont pas désirées ! *)
  let (obj, constr, l_var) = ctx in
  let l_champs =
    (List.rev_map (fun x -> x.var_id) cl.class_members)
  in
  if not (check_name l_champs) then
    raise (Typing_Error((localisation cl.class_loc) ^ (sprintf "Des champs de la classe %s ont le même nom !" cl.class_id)));
  (ObjSet.add cl.class_id cl obj, constr, l_var)
;;

let type_file f file_name =
  file := file_name;
  rename_cons_arg f.class_def; (* On renomme les paramètres de classe *)
  let rec check_class l_cl ctx =
    match l_cl with
    |[] -> ctx
    |h::t -> check_class t (type_class h ctx)
  in
  let l_class_def = f.class_def @ [f.main] in
  
  if not (check_name (List.map (fun x -> x.class_id) l_class_def)) then
    raise (Typing_Error("Définition multiple d'une même classe !"));
  
  if not (List.for_all
       (fun x -> match x.class_extend with
                 |TAnyRef |TType(_, _) -> true
                 |_ -> false) l_class_def) then
    raise (Typing_Error("Une classe ne peut hérité d'un type primitif excepté d'AnyRef !"));
    
  check_class l_class_def (ObjSet.empty, ObjConstr.empty, []);
  let ma_class_main = f.main in
  try
    let ma_f_main = List.find (fun x -> x.method_id = "main") ma_class_main.class_methods in
    if ma_f_main.method_param_type <> [] then
      raise (Typing_Error((localisation ma_class_main.class_loc) ^ "La fonction main a des paramètres de types !"));
    match ma_f_main.method_param with
    |[{param_id = _; param_ty = TType("Array", [TString])}] -> ()
    |_ -> raise (Typing_Error((localisation ma_class_main.class_loc) ^ "La fonction main a des paramètres invalides !"));
    if ma_f_main.method_out_ty <> TUnit then
      raise (Typing_Error((localisation ma_class_main.class_loc) ^ "La fonction main a un type de retour invalide !"))
  with Not_found -> raise (Typing_Error((localisation ma_class_main.class_loc) ^ "La classe Main n'a pas de fonction main !"))
;;
















































