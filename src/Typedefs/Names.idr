module Typedefs.Names

import Prelude.Chars
import Prelude.Strings

%default total
%access public export

Name : Type
Name = String

uppercase : Name -> Name
uppercase n with (strM n)
  uppercase (strCons x xs) | (StrCons x xs) = strCons (toUpper x) xs
  uppercase _              | _              = ""

lowercase : Name -> Name
lowercase n with (strM n)
  lowercase (strCons x xs) | (StrCons x xs) = strCons (toLower x) xs
  lowercase _              | _              = ""
