all: test test2

test: test_pas_a_pas.ml projet_logique.ml
	ocamlc projet_logique.ml test_pas_a_pas.ml -o exc
	./exc

test2: test_pas_a_pas_2.ml projet_logique.ml
	ocamlc projet_logique.ml test_pas_a_pas_2.ml -o exc
	./exc

test3: test_3.ml projet_logique.ml
	ocamlc projet_logique.ml test_3.ml -o exc
	./exc

clean:
	rm exc
	rm projet_logique.cmi
	rm projet_logique.cmo
	rm test_pas_a_pas.cmi
	rm test_pas_a_pas.cmo
	rm test_pas_a_pas_2.cmi
	rm test_pas_a_pas_2.cmo
	rm test_3.cmi
	rm test_3.cmo
