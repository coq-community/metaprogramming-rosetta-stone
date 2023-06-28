build:
	# building elpi #####################
	make -C elpi
	# building ltac2 #####################
	coqc -Q ltac2 Autoinduct ltac2/Autoinduct.v
	# building ltac1 #####################
	coqc -Q ltac1 Autoinduct ltac1/Autoinduct.v

test:
	# testing elpi #####################
	coqc -Q elpi/theories Autoinduct Test.v
	# testing ltac2 #####################
	coqc -Q ltac2 Autoinduct Test.v
	# testing ltac1 #####################
	coqc -Q ltac1 Autoinduct Test.v

clean:
	make -C elpi clean
	rm -f ltac2/Autoinduct.vo
	rm -f ltac1/Autoinduct.vo