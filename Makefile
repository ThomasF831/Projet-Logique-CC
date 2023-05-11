all: tests

tests: tests.ml projet_logique.ml
	ocamlc projet_logique.ml tests.ml -o exc
	./exc

clean: exc projet_logique.cmi projet_logique.cmo tests.cmi tests.cmo
	rm exc
	rm projet_logique.cmi
	rm projet_logique.cmo
	rm tests.cmi
	rm tests.cmo
