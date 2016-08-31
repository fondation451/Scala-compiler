{
  open Scala_spec
  open Scala_parser
  open Lexing
  
  exception Lexical_error of string;;
  
  let keywords = Hashtbl.create 97
  let () = List.iter (fun (x, y) -> Hashtbl.add keywords x y)
             ["class", CLASS ; "def", DEF ; "else", ELSE ; "eq", EQ ; "extends", EXTENDS ; "false", FALSE ;
              "if", IF ; "ne", NE ; "new", NEW ; "null", NULL ; "object", OBJECT ; "override", OVERRIDE ;
              "print", PRINT ; "return", RETURN ; "this", THIS ; "true", TRUE ; "val", VAL ; "var", VAR ;
              "while", WHILE ; "Main", MAIN]
  
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      {pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum}
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let car = [' '-'!' '#'-'[' ']'-'~'] | "\\\\" | "\\\"" | "\\n" | "\\t"

let ident = letter (letter | digit | '_')*
let integer = '0' | ['1'-'9'] digit*
let str = '"' car* '"'

rule next_tokens = parse
  |"\n" {newline lexbuf; next_tokens lexbuf}
  |[' ' '\t']+ {next_tokens lexbuf} (* Gestion des blancs *)
  |integer as str_n
    {try
       let nb = int_of_string str_n in
       if nb < (1 lsl 31) then
         INTEGER(nb)
       else
         raise (Lexical_error "Constante entière trop grande !")
     with
       |Failure s -> raise (Lexical_error "Constante entière trop grande !")}
  |ident as str_id {try Hashtbl.find keywords str_id with Not_found -> IDENT(str_id)}
  |str as s {STRING_CONST(s)}
  |"=" {AFFECTATION}
  |"==" {PHYSICAL_EQ}
  |"!=" {PHYSICAL_NE}
  |"<=" {LESS_EQ}
  |">=" {GREATER_EQ}
  |"+" {PLUS}
  |"-" {SUB}
  |"*" {TIMES}
  |"/" {DIV}
  |"%" {MOD}
  |"&&" {AND}
  |"||" {OR}
  |"!" {NOT}
  |"." {ACCESS}
  |":" {COLON}
  |"," {COMMA}
  |";" {SEMI_COLON}
  |"(" {OPEN_BRACKET}
  |")" {CLOSE_BRACKET}
  |"<" {OPEN_BALISE}
  |">" {CLOSE_BALISE}
  |"[" {OPEN_SQ_BRACKET}
  |"]" {CLOSE_SQ_BRACKET}
  |"{" {OPEN_BRACE}
  |"}" {CLOSE_BRACE}
  |"<:" {LOWER_CONSTRAINT}
  |">:" {UPPER_CONSTRAINT}
  |"/*" {comment_block lexbuf}
  |"//" {comment_line lexbuf}
  |eof {EOF}
  |_ {raise (Lexical_error "")}

and comment_block = parse
  |"*/" {next_tokens lexbuf}
  |_ {comment_block lexbuf}
  |eof {raise (Lexical_error "Commentaire non terminé !\n")}

and comment_line = parse
  |"\n" {next_tokens lexbuf}
  |_ {comment_line lexbuf}
  |eof {EOF}
  















































