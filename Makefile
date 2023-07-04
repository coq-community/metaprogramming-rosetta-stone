all: test

build:
	make -C autoinduct build

test: build
	make -C autoinduct test

install:
	echo "This project is not to be installed"
	exit 1
