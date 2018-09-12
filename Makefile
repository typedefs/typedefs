pkg=

all: build-all doc-all test-all

build-all:
	make build pkg=typedefs
	make build pkg=typedefs-examples
	make build pkg=typedefs-parser
	make build pkg=typedefs-parser-js

doc-all:
	make doc pkg=typedefs

test-all:
	make test pkg=typedefs

clean-all:
	make clean pkg=typedefs
	make clean pkg=typedefs-examples
	make clean pkg=typedefs-parser
	make clean pkg=typedefs-parser-js

build: src
	idris --build ${pkg}.ipkg

install: src
	idris --install ${pkg}.ipkg

test: src
	idris --testpkg ${pkg}.ipkg

doc: src
	idris --mkdoc ${pkg}.ipkg

clean:
	idris --clean ${pkg}.ipkg

repl:
	idris -i src

nix:
	if [ -z "${pkg}" ];		\
	then nix-build;			\
	else nix-build -A ${pkg};	\
	fi
