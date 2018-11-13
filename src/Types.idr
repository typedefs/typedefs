module Types

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

{-
A bit ugly but works, but the Maybe has to be dealt with in Parse.idr

data Name = MkName Char String

mkName : String -> Maybe Name
mkName s with (strM s)
  mkName (strCons x xs) | (StrCons x xs) = Just (MkName x xs)
  mkName ""             | StrNil         = Nothing

uppercase : Name -> Name
uppercase (MkName x xs) = MkName (toUpper x) xs

lowercase : Name -> Name
lowercase (MkName x xs) = MkName (toLower x) xs

Show Name where
  show (MkName x xs) = strCons x xs
-}


{-
Not practical because x and xs cannot be inferred in all cases.

Name : {x : Char} -> {xs : String} -> Type
Name {x} {xs} = StrM (strCons x xs)

uppercase : Name {x} {xs} -> Name {x=toUpper x} {xs}
uppercase {x} {xs} _ = StrCons (toUpper x) xs

lowercase : Name {x} {xs} -> Name {x=toLower x} {xs}
lowercase {x} {xs} _ = StrCons (toLower x) xs

mkName : String -> Name
mkName "" = ?noname
mkName s  = strM _
-}