

all: spec type parser_inter parser_compil lexer_compil x86_64_inter x86_64 compile main
	ocamlc -annot -g -o pscala nums.cma scala_spec.cmo scala_type.cmo scala_lexer.cmo scala_parser.cmo x86_64.cmo scala_compile.cmo main.cmo

main:
	ocamlc -annot -g -c main.ml

lexer:
	ocamllex scala_lexer.mll

parser:
	menhir --infer --explain -v scala_parser.mly

spec:
	ocamlc -annot -g -c scala_spec.ml

type:
	ocamlc -annot -g -c scala_type.ml
	
parser_compil: parser
	ocamlc -annot -g -c scala_parser.ml

parser_inter: parser
	ocamlc -annot -g -c scala_parser.mli
	
lexer_compil: lexer
	ocamlc -annot -g -c scala_lexer.ml

x86_64_inter:
	ocamlc -annot -g -c x86_64.mli

x86_64:
	ocamlc -annot -g -c x86_64.ml

compile: x86_64
	ocamlc -annot -g -c scala_compile.ml

clean:
	rm -f *.cm[io] *.o *.annot *~ pscala scala_lexer.ml scala_parser.ml scala_parser.mli
	rm -f *.output *.automaton
