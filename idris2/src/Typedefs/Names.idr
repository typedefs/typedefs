module Typedefs.Names

import Data.String

%default total

public export
Name : Type
Name = String

export
uppercase : Name -> Name
uppercase n with (strM n)
  uppercase (strCons x xs) | (StrCons x xs) = strCons (toUpper x) xs
  uppercase _              | _              = ""

export
lowercase : Name -> Name
lowercase n with (strM n)
  lowercase (strCons x xs) | (StrCons x xs) = strCons (toLower x) xs
  lowercase _              | _              = ""
