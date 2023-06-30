build: build-elpi build-ltac2 build-ltac1 build-ocaml build-metacoq

build-elpi:
	# building elpi #####################
	make -C elpi

build-ltac2:
	# building ltac2 #####################
	coqc -Q ltac2 Ltac2.Autoinduct ltac2/Autoinduct.v

build-ltac1:
	# building ltac1 #####################
	coqc -Q ltac1 Ltac1.Autoinduct ltac1/Autoinduct.v

build-ocaml:
	# building ocaml #####################
	make -C ocaml

build-metacoq:
	# building metacoq #####################
	make -C metacoq

install: install-elpi install-ocaml install-metacoq

install-elpi:
	# installing elpi #####################
	make -C elpi install

# install-ltac2:
# 	# installing ltac2 #####################
# 	coqc -Q ltac2 Ltac2.Autoinduct ltac2/Autoinduct.v

# install-ltac1:
# 	# installing ltac1 #####################
# 	coqc -Q ltac1 Ltac1.Autoinduct ltac1/Autoinduct.v

install-ocaml:
	# installing ocaml #####################
	make -C ocaml install

install-metacoq:
	# installing metacoq #####################
	make -C metacoq install

test: test-elpi test-ltac2 test-ltac1 test-ocaml test-metacoq

test-elpi:
	# testing elpi #####################
	coqc -Q elpi/theories Elpi.Autoinduct Test.v

test-ltac2:	
	# testing ltac2 #####################
	coqc -Q ltac2 Ltac2.Autoinduct Test.v

test-ltac1:
	# testing ltac1 #####################
	coqc -Q ltac1 Ltac2.Autoinduct Test.v

test-ocaml:
	# testing ocaml #####################
	OCAMLPATH=$$OCAMLPATH:$$PWD/ocaml/ coqc -I ocaml/src -Q ocaml/theories OCaml.Autoinduct Test.v

test-metacoq:
	# testing metacoq #####################
	coqc -Q metacoq/theories MetaCoq.Autoinduct Test.v

clean:
	make -C elpi clean
	rm -f ltac2/Autoinduct.vo
	rm -f ltac1/Autoinduct.vo
