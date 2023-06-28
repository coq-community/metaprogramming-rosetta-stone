build:
	# elpi
	make -C elpi
	# ltac2
	coqc -Q ltac2 Autoinduct ltac2/Autoinduct.v

test: build
	coqc -Q elpi/theories Autoinduct Test.v
	coqc -Q ltac2 Autoinduct Test.v

clean:
	make -C elpi clean
	rm -f ltac2/Autoinduct.vo