(* Type de Syntaxe abstraite *)

type sc_file = {
  class_def : sc_class list;
  main : sc_class;
}

and sc_class = {
  class_id : string;
  class_param_type : sc_param_ty list;
  class_param : sc_param list;
  class_extend : type_system;
  class_extend_expr : sc_expr_dec list;
  mutable class_body : sc_decl list;
  mutable class_members : sc_var list;
  mutable class_methods : sc_method list;
  class_loc : Lexing.position * Lexing.position;
}

and sc_decl =
  |Decl_Var of sc_var
  |Decl_Meth of sc_method

and sc_var = {
  var_id : string;
  mutable var_ty : type_system;
  mutable var_v  : sc_expr_dec;
  var_mut : bool; (* true si mutable, false sinon *)
}

and sc_method = {
  method_id : string;
  method_param_type : sc_param_ty list;
  method_param : sc_param list;
  method_out_ty : type_system;
  mutable method_body : sc_expr_dec;
  method_override : bool; (* true si override *)
  mutable method_obj : string;
  method_loc : Lexing.position * Lexing.position;
}

and sc_param = {
  mutable param_id : string;
  param_ty : type_system;
}

and sc_param_ty = {
  param_ty_variancy : un_constraint list;
  param_ty_id : string;
  param_ty_constr : bin_constraint list;
  param_ty_ty : type_system list;
}

and bin_constraint =
  |Sc_Lower_Constr
  |Sc_Upper_Constr


and un_constraint =
  |Sc_Plus_Constr
  |Sc_Sub_Constr
  |Sc_Neutre_Constr

and sc_expr_dec = {
  desc : sc_expr;
  loc : Lexing.position * Lexing.position;
  e_ty : type_system;
}

and sc_expr =
  |EInteger of int
  |EString of string
  |EBool of bool
  |ENull
  |EThis
  |EUnit
  |EAccess of sc_access
  |EAffectation of sc_access * sc_expr_dec
  |ECall of sc_expr_dec * string * type_system list * sc_expr_dec list
  |EInstanciation of string * type_system list * sc_expr_dec list
  |ENot of sc_expr_dec
  |ENeg of sc_expr_dec
  |EOp of sc_expr_dec * sc_op * sc_expr_dec
  |EIfThenElse of sc_expr_dec * sc_expr_dec * sc_expr_dec
  |EWhile of sc_expr_dec * sc_expr_dec
  |EReturn of sc_expr_dec
  |Eprint of sc_expr_dec
  |EBlock of sc_block list
and sc_block =
  |Block_Var of sc_var
  |Block_Expr of sc_expr_dec
and sc_op =
  |Op_Eq |Op_Ne |Op_Physical_Eq |Op_Physical_Ne
  |Op_Less |Op_Less_Eq |Op_Greater |Op_Greater_Eq
  |Op_Add |Op_Sub |Op_Mul |Op_Div |Op_Mod |Op_And |Op_Or
and sc_access =
  |Access_Ident of string
  |Access_Point of sc_expr_dec * string

(* Type pour le typage  *)
and type_system =
  |TNone (* Expression pas encore typée *)
  |TAny
  |TAnyVal
  |TBoolean
  |TInt
  |TUnit
  |TAnyRef
  |TString
  |TNull
  |TNothing
  |TType of string * type_system list
;;

module ObjSet = Map.Make(String);; (* Stocke les classes déjà typées *)
module ObjConstr = Map.Make(String);; (* Stocke des contraintes *)

type context_type = sc_class ObjSet.t * ((bin_constraint * type_system) list) ObjConstr.t * sc_var list;;







































