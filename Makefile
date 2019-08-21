pkg=

all: build-all doc-all test-all

build-all: build-lib install-lib build-rest

build-lib:
	make build pkg=typedefs-core

build-rest:
	make build pkg=typedefs-examples
	make build pkg=typedefs-core
	make build pkg=typedefs-js

doc-all:
	make doc pkg=typedefs-core

test-all:
	make test pkg=typedefs-core

install-lib:
	make install pkg=typedefs-core

install-all:
	make install pkg=typedefs
	make install pkg=typedefs-examples
	make install pkg=typedefs-core
	make install pkg=typedefs-js

clean-all:
	make clean pkg=typedefs
	make clean pkg=typedefs-examples
	make clean pkg=typedefs-core
	make clean pkg=typedefs-js

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
