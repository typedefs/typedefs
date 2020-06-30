module NEList

public export
record NEList (t : Type) where
  constructor MkNEList
  head : t
  tail : List t

