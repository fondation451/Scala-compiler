open Scala_spec;;
open Scala_parser;;
open Scala_lexer;;
open Scala_compile;;
open Format;;
open Lexing;;

let parse_only = ref false;;
let type_only = ref false;;

let verbose_on = ref false;;

let input_file = ref "";;
let output_file = ref "";;

let usage = "usage: mon_scala [option] file.sc";;

let set_file f s = f := s;;

let options =
  ["--parse-only", Arg.Set parse_only, "  Pour ne faire uniquement que la phase d'analyse syntaxique";
   "--type-only", Arg.Set type_only, "  Pour ne faire uniquement que la phase d'analyse sémantique";
   "-v", Arg.Set verbose_on, "  Pour avoir un peu de texte dans la compilation"]
;;

let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !input_file l (c-1) c
;;

let () =
  Arg.parse options (set_file input_file) usage;
  
  if !input_file = "" then begin
    eprintf "Aucun fichier à compiler\n@?";
    exit 1 end;
  
  let f = open_in !input_file in
  let buf = Lexing.from_channel f in
  
  try
    let p = Scala_parser.file Scala_lexer.next_tokens buf in
    close_in f;
    if !parse_only then exit 0;
    
    Scala_type.type_file p !input_file;
    if !type_only then exit 0;
    if !verbose_on then
      Printf.printf "Typage Terminé !\n"; 
    
    let output_file = (String.sub (!input_file) 0 (String.length (!input_file) - 5)) ^ "s" in
    compile_program p output_file;
    
    if !verbose_on then
      Printf.printf "Compilation Terminé !\n";
    
    exit 0;
  with
    |Lexical_error(str) ->
      (localisation (Lexing.lexeme_start_p buf);
      eprintf "Erreur Lexical@.";
      Printf.printf "%s\n" str;
      exit 1)
    |Scala_parser.Error ->
      (localisation (Lexing.lexeme_start_p buf);
      eprintf "Erreur syntaxique@.";
      exit 1)
    |Scala_type.Typing_Error(str) ->
      (Printf.printf "%s\n" str;
       exit 1)
    |Scala_type.Typing_Exception(str) ->
      (Printf.printf "%s\n" str;
       exit 2)
    |_ -> exit 1
;;



































