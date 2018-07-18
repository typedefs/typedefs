sources=src
executable=examples

all: build ${executable}

build: ${sources}
	idris --build typedefs.ipkg
install: ${sources}
	idris --install typedefs.ipkg
test:
	idris --testpkg typedefs.ipkg
repl: ${sources}
	idris ${sources}
doc:
	idris --mkdoc typedefs.ipkg
clean:
	idris --clean typedefs.ipkg

${executable}: ${sources}
	idris --build typedefs-examples.ipkg
run:
	./${executable}
