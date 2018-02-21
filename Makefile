sources=Types.idr Token.idr Lex.idr AST.idr Parse.idr typedefs.idr
timestamp=`date +"%y%m%d-%H%M"`
backupfile=typedefs-sources-${timestamp}.tar

# native
typedefs: ${sources}
	idris -p contrib ${sources} -o typedefs

test:
	./typedefs

repl: ${sources}
	idris ${sources}

# TODO fix totality error (workaround: comment out '%default total')
node: ${sources}
	idris --codegen node -p contrib ${sources} -o typedefs-js

backup:
	echo ${timestamp}
	tar cvf ${backupfile} ${sources}
	gzip ${backupfile}
