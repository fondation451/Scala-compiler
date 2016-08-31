%{
  open Scala_spec
  
  exception Mon_Erreur;;
  
  let rec filter_var l_decl out =
    match l_decl with
    |[] -> out
    |Decl_Var(v)::t -> filter_var t (v::out)
    |Decl_Meth(m)::t -> filter_var t out
  ;;
  
  let rec filter_meth l_decl out =
    match l_decl with
    |[] -> out
    |Decl_Var(v)::t -> filter_meth t out
    |Decl_Meth(m)::t -> filter_meth t (m::out)
  ;;
  
  let kw = Hashtbl.create 97
  let () = List.iter (fun (x, y) -> Hashtbl.add kw x y)
             ["Any", TAny ; "AnyVal", TAnyVal ; "Boolean", TBoolean ;
              "Int", TInt ; "Unit", TUnit ; "AnyRef", TAnyRef ;
              "String", TString ; "Null", TNull ; "Nothing", TNothing]
%}


%token CLASS DEF ELSE EQ EXTENDS FALSE IF NE NEW NULL OBJECT OVERRIDE PRINT RETURN THIS TRUE VAL VAR WHILE MAIN
%token <int> INTEGER
%token <string> IDENT
%token <string> STRING_CONST
%token PHYSICAL_EQ PHYSICAL_NE LESS_EQ GREATER_EQ AFFECTATION
%token PLUS SUB TIMES DIV MOD AND OR NOT ACCESS
%token COLON COMMA SEMI_COLON OPEN_BRACKET CLOSE_BRACKET
%token OPEN_BALISE CLOSE_BALISE OPEN_SQ_BRACKET CLOSE_SQ_BRACKET
%token OPEN_BRACE CLOSE_BRACE LOWER_CONSTRAINT UPPER_CONSTRAINT
%token EOF

%left struct_prec
%left RETURN
%left AFFECTATION
%left OR
%left AND
%left EQ NE PHYSICAL_EQ PHYSICAL_NE
%left OPEN_BALISE CLOSE_BALISE LESS_EQ GREATER_EQ
%left PLUS SUB
%left TIMES DIV MOD
%left NOT
%left ACCESS

%nonassoc uminus
%nonassoc ELSE

%start file

%type <Scala_spec.sc_file> file

%%

file:
  |c = classe*; OBJECT; MAIN; OPEN_BRACE; my_main = separated_list(SEMI_COLON, decl); CLOSE_BRACE; EOF
    {{class_def = c;
      main =
        {class_id = "Main";
         class_param_type = [];
         class_param = [];
         class_extend = TAnyRef;
         class_extend_expr = [];
         class_body = my_main;
         class_members = [];
         class_methods = [];
         class_loc = ($startpos, $endpos);
        };
    }}
;

classe:
  |CLASS; id = IDENT; t1 = option(param_ty_class_with_sq_br); t2 = option(param_with_br); ext = option(extend_option); OPEN_BRACE; cl_body = separated_list(SEMI_COLON, decl); CLOSE_BRACE
    {{class_id = id;
      class_param_type =
        (match t1 with
        |None -> []
        |Some x -> x);
      class_param =
        (match t2 with
        |None -> []
        |Some x -> x);
      class_extend =
        (match ext with
        |None -> TAnyRef
        |Some(t, e_p) -> t);
      class_extend_expr =
        (match ext with
        |None -> []
        |Some(t, e_p) -> e_p);
      class_body = cl_body;
      class_members = [];
      class_methods = [];
      class_loc = ($startpos, $endpos);
    }}
;

extend_expr_with_br:
  |OPEN_BRACKET; l_e = separated_list(COMMA, expr); CLOSE_BRACKET
    {l_e}
;

extend_option:
  |EXTENDS; t = ty; e_p = option(extend_expr_with_br)
    {match e_p with
       |None -> (t, [])
       |Some x -> (t, x);
    }
;

param_ty_class_with_sq_br:
  |OPEN_SQ_BRACKET; t = separated_nonempty_list(COMMA, param_ty_class); CLOSE_SQ_BRACKET
    {t}
;

param_with_br:
  |OPEN_BRACKET; t = separated_list(COMMA, param); CLOSE_BRACKET
    {t}
;


decl:
  |v = var {Decl_Var(v)}
  |m = methods {Decl_Meth(m)}
;

var_mutability:
  |VAR {true}
  |VAL {false}
;

ty_with_colon:
  |COLON t = ty {t}
;

var:
  |v = var_mutability; id = IDENT; t = option(ty_with_colon); AFFECTATION; e = expr
    {{var_id = id;
      var_ty =
        (match t with
        |None -> TNone
        |Some x -> x);
      var_v = e;
      var_mut = v;
    }}
;

methods_body:
  |OPEN_BRACE; b = separated_list(SEMI_COLON, block); CLOSE_BRACE
    {TUnit, {desc = EBlock(b); loc = ($startpos, $endpos); e_ty = TNone}}
  |COLON; t = ty; AFFECTATION; e = expr
    {t, e}
;

param_ty_with_sq_br:
  |OPEN_SQ_BRACKET; p_t = separated_nonempty_list(COMMA, param_ty); CLOSE_SQ_BRACKET
    {p_t}
;

methods:
  |over = option(OVERRIDE); DEF; id = IDENT; p_t = option(param_ty_with_sq_br); OPEN_BRACKET; p = separated_list(COMMA, param); CLOSE_BRACKET; m_body = methods_body
     {{method_id = id;
       method_param_type =
         (match p_t with
         |None -> []
         |Some x -> x);
       method_param = p;
       method_out_ty = fst m_body;
       method_body = snd m_body;
       method_override =
         (match over with
         |None -> false
         |Some x -> true);
       method_obj = "";
       method_loc = ($startpos, $endpos);
     }}
;

param:
  |id = IDENT COLON t = ty
    {{param_id = id; 
      param_ty = t;
    }}
;

type_constraint:
  |LOWER_CONSTRAINT {Sc_Lower_Constr}
  |UPPER_CONSTRAINT {Sc_Upper_Constr}
;

ty_with_type_constraint:
  |lw_c = type_constraint; t = ty
    {lw_c, t}
;

param_ty:
  |id = IDENT; constr_ty = option(ty_with_type_constraint)
    {match constr_ty with
      |None ->
        {param_ty_variancy = [];
         param_ty_id = id;
         param_ty_constr = [];
         param_ty_ty = [];
        }
      |Some x ->
        {param_ty_variancy = [];
         param_ty_id = id;
         param_ty_constr = [fst x];
         param_ty_ty = [snd x];
        };
    }
;

variancy:
  |PLUS {Sc_Plus_Constr}
  |SUB {Sc_Sub_Constr}
;

param_ty_class:
  |s = option(variancy) p_t = param_ty
    {{param_ty_variancy =
       (match s with
        |None -> []
        |Some x -> [x]);
      param_ty_id = p_t.param_ty_id;
      param_ty_constr = p_t.param_ty_constr;
      param_ty_ty = p_t.param_ty_ty;
    }}
;

ty:
  |id = IDENT arg_t = arg_ty
    {try
       let out = Hashtbl.find kw id in
       out
       (*if arg_t = [] then
         out
       else
         raise Mon_Erreur*) (* Gerer le cas ou un type de base est paramétré PAS BON !!! *)
     with
       Not_found -> TType(id, arg_t)
    }
;

arg_ty_inside:
  |OPEN_SQ_BRACKET; t = separated_nonempty_list(COMMA, ty); CLOSE_SQ_BRACKET
    {t}
;

arg_ty:
  |t = option(arg_ty_inside)
    {match t with
       |None -> []
       |Some x -> x;
    }
;

%inline binop:
  |EQ {Op_Eq}
  |NE {Op_Ne}
  |PHYSICAL_EQ {Op_Physical_Eq}
  |PHYSICAL_NE {Op_Physical_Ne}
  |LESS_EQ {Op_Less_Eq}
  |GREATER_EQ {Op_Greater_Eq}
  |PLUS {Op_Add}
  |SUB {Op_Sub}
  |TIMES {Op_Mul}
  |DIV {Op_Div}
  |MOD {Op_Mod}
  |AND {Op_And}
  |OR {Op_Or}
  |OPEN_BALISE {Op_Less} 
  |CLOSE_BALISE {Op_Greater}
;

access:
  |id = IDENT
    {Access_Ident(id)}
  |e = expr; ACCESS; id = IDENT
    {Access_Point(e, id)}
;

block:
  |v = var
    {Block_Var(v)}
  |e = expr
    {Block_Expr(e)}
;

expr:
  |i = INTEGER {{desc = EInteger(i); loc = ($startpos, $endpos); e_ty = TNone}}
  |str = STRING_CONST {{desc = EString(str); loc = ($startpos, $endpos); e_ty = TNone}}
  |TRUE {{desc = EBool(true); loc = ($startpos, $endpos); e_ty = TNone}}
  |FALSE {{desc = EBool(false); loc = ($startpos, $endpos); e_ty = TNone}}
  |OPEN_BRACKET; CLOSE_BRACKET {{desc = EUnit; loc = ($startpos, $endpos); e_ty = TNone}}
  |THIS {{desc = EThis; loc = ($startpos, $endpos); e_ty = TNone}}
  |NULL {{desc = ENull; loc = ($startpos, $endpos); e_ty = TNone}}
  |OPEN_BRACKET; e = expr; CLOSE_BRACKET {e}
  |a = access {{desc = EAccess(a); loc = ($startpos, $endpos); e_ty = TNone}}
  |a = access; AFFECTATION; e = expr {{desc = EAffectation(a, e); loc = ($startpos, $endpos); e_ty = TNone}}
  |a = access; a_t = arg_ty; OPEN_BRACKET; e = separated_list(COMMA, expr); CLOSE_BRACKET
    {match a with
     |Access_Point(exp, str) -> {desc = ECall(exp, str, a_t, e); loc = ($startpos, $endpos); e_ty = TNone}
     |Access_Ident(str) -> {desc = ECall({desc = EThis; loc = ($startpos, $endpos); e_ty = TNone}, str, a_t, e); loc = ($startpos, $endpos); e_ty = TNone}
    }
  |NEW; id = IDENT; a_t = arg_ty; OPEN_BRACKET; e = separated_list(COMMA, expr); CLOSE_BRACKET
    {{desc = EInstanciation(id, a_t, e); loc = ($startpos, $endpos); e_ty = TNone}}
  |NOT; e = expr; {{desc = ENot(e); loc = ($startpos, $endpos); e_ty = TNone}}
  |SUB; e = expr %prec uminus {{desc = ENeg(e); loc = ($startpos, $endpos); e_ty = TNone}}
  |e1 = expr; o = binop; e2 = expr; {{desc = EOp(e1, o, e2); loc = ($startpos, $endpos); e_ty = TNone}}
  |IF; OPEN_BRACKET; e1 = expr; CLOSE_BRACKET; e2 = expr %prec struct_prec
    {{desc = EIfThenElse(e1, e2, {desc = EUnit; loc = ($startpos, $endpos); e_ty = TNone}); loc = ($startpos, $endpos); e_ty = TNone}}
  |IF; OPEN_BRACKET; e1 = expr; CLOSE_BRACKET; e2 = expr; ELSE; e3 = expr %prec struct_prec
    {{desc = EIfThenElse(e1, e2, e3); loc = ($startpos, $endpos); e_ty = TNone}}
  |WHILE; OPEN_BRACKET; e1 = expr; CLOSE_BRACKET; e2 = expr %prec struct_prec
    {{desc = EWhile(e1, e2); loc = ($startpos, $endpos); e_ty = TNone}}
  |RETURN; e = expr
    {{desc = EReturn(e); loc = ($startpos, $endpos); e_ty = TNone}}
  |RETURN
    {{desc = EReturn({desc = EUnit; loc = ($startpos, $endpos); e_ty = TNone}); loc = ($startpos, $endpos); e_ty = TNone}}
  |PRINT; OPEN_BRACKET; e = expr; CLOSE_BRACKET
    {{desc = Eprint(e); loc = ($startpos, $endpos); e_ty = TNone}}
  |OPEN_BRACE; b = separated_list(SEMI_COLON, block); CLOSE_BRACE
    {{desc = EBlock(b); loc = ($startpos, $endpos); e_ty = TNone}}
;








































