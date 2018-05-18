executable=examples

${executable}: src
	idris --build typedefs.ipkg
run:
	./${executable}
test:
	idris --testpkg typedefs.ipkg
repl: ${sources}
	idris ${sources}
doc:
	idris --mkdoc typedefs.ipkg
clean:
	idris --clean typedefs.ipkg
