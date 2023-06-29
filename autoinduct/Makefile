build:
	# building elpi #####################
	make -C elpi
	# building ltac2 #####################
	coqc -Q ltac2 Autoinduct ltac2/Autoinduct.v
	# building ltac1 #####################
	coqc -Q ltac1 Autoinduct ltac1/Autoinduct.v
	# building ocaml #####################
	make -C ocaml
	# building metacoq #####################
	make -C metacoq

test: test-elpi test-ltac2 test-ltac1 test-ocaml

test-elpi:
	# testing elpi #####################
	coqc -Q elpi/theories Autoinduct Test.v
test-ltac2:	
	# testing ltac2 #####################
	coqc -Q ltac2 Autoinduct Test.v
test-ltac1:
	# testing ltac1 #####################
	coqc -Q ltac1 Autoinduct Test.v
test-ocaml:
	# testing ocaml #####################
	OCAMLPATH=$$OCAMLPATH:$$PWD/ocaml/ coqc -I ocaml/src -Q ocaml/theories Autoinduct Test.v

clean:
	make -C elpi clean
	rm -f ltac2/Autoinduct.vo
	rm -f ltac1/Autoinduct.vo