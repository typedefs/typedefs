example, `idris typedefs.idr`:

	*typedefs> showTDef list
	"list = mu [nil: 1, cons: ({1} * {0})]" : String
	*typedefs> showTDef maybe
	"(1 + {0})" : String
