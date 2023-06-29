build: build-elpi build-ltac2 build-ltac1 build-ocaml build-metacoq

build-elpi:
	# building elpi #####################
	make -C elpi

build-ltac2:
	# building ltac2 #####################
	coqc -Q ltac2 Autoinduct ltac2/Autoinduct.v

build-ltac1:
	# building ltac1 #####################
	coqc -Q ltac1 Autoinduct ltac1/Autoinduct.v

build-ocaml:
	# building ocaml #####################
	make -C ocaml

build-metacoq:
	# building metacoq #####################
	make -C metacoq

test: test-elpi test-ltac2 test-ltac1 test-ocaml test-metacoq

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

test-metacoq:
	# testing metacoq #####################
	coqc -Q metacoq/theories Autoinduct Test.v

clean:
	make -C elpi clean
	rm -f ltac2/Autoinduct.vo
	rm -f ltac1/Autoinduct.vo