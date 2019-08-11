
# Typedefs binary format

Terms are serialised in a type-directed way, given a Typedefs
description --- terms make no sense on their own. If the type is
unknown, a description of the type could first be serialised, followed
by the serialisation of the term --- this is future work.

Terms are serialised as follows:

- Terms of type `T0` or `T1` do not need to be serialised --- the former does not exist, and the latter are trivial.
- Terms of type `TSum ts` with `|ts| = 2 + k` are serialised as an integer `i` (with `i < 2 + k`, but this is not exploited), followed by the serialisation of a term of type `ts[i]`.
- Terms of type `TProd ts` with `|ts| = 2 + k` are serialised as the serialisation of `ts[0]`, ..., `ts[1+k]`. This relies on being able to compute the width of each serialised term.
- Terms of type `Tvar j` are serialised with a given "parameter" serialiser --- this is used to serialise `TMu`s.
- Terms of type `TMu ts` with |ts| = k are serialised as an integer `i` (with `i < k`, but this is not exploited), followed by the serialisation of a term of type ts[i], where the "parameter" serialiser for the new type variable is instantiated to this described procedure.
- Terms of type `TApp f xs` with `|xs| = k` are serialised as terms of type `f`, with "parameter" serialisers given by the `k` serialisations of terms of type `xs[k]`.


# Example

Given this typedef:

```
(name Boolean (mu (True 1) (False 1)))

(name Try (+ (var 0) (var 1)))

(name LinkedList (mu (Nil 1) (Cons (* (var 1) (var 0)))))
```
_You can find this definition in the `example.tdef` file_

We can generate a new Haskell file that will define those types in Haskell and will create serialisers and
deserialisers for terms of those types.

We generate the Haskell code using the `typedefs` command line tool. See the [installation tutorial][INSTALL].

```
typedefs -s example.tdef -d example.hs
```

You can find the generated file in this repo at `docs/Binary format/example.hs`<sup>[1](#footnote)</sup>

## Interacting with Haskell


In order to use Typedefs, you need to import its definitions in your codebase.

Here is an example of a Haskell file that imports the Typedefs definitions and uses them for serialising and
deserialising terms that correspond to the specified types:


```haskell
module Main where

import Example as E
import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder

false = E.False
true = E.True

displayBytes :: B.ByteString -> String
displayBytes = concatMap show . B.unpack

listBool = Cons false (Cons true (Cons false Nil))

encodeBool :: Boolean -> B.ByteString
encodeBool = toLazyByteString . encodeBoolean

encodeList :: LinkedList Boolean -> B.ByteString
encodeList = toLazyByteString . encodeLinkedList encodeBoolean 

encodeTry :: Try Boolean (LinkedList Boolean) -> B.ByteString
encodeTry = toLazyByteString . E.encodeTry encodeBoolean (encodeLinkedList encodeBoolean)

success = Right listBool

main :: IO ()
main = do print $ "true : " ++ (displayBytes $ encodeBool true)
          print $ "false : " ++ (displayBytes $ encodeBool false)
          let value = false
          let encoded = encodeBool value
          print $ displayBytes encoded
          let decoded = runDeserialiser decodeBoolean encoded
          print $ decoded
          case decoded of
            Nothing -> print "decoding failed"
            Just (d, _) -> if d == value then print "decoding succeeded"
                                         else print "values are inconsistent"
          let encodedList = encodeList listBool
          print $ displayBytes encodedList
          let decodedList = runDeserialiser (decodeLinkedList decodeBoolean) encodedList
          case decodedList of
            Nothing -> print "decoding failed"
            Just (d, _) -> if d == listBool then print "decoding succeeded"
                                            else print "values are inconsistent"
          let encodedTry = Main.encodeTry success
          print $ displayBytes encodedTry
          let decodedTry = runDeserialiser (decodeTry decodeBoolean (decodeLinkedList decodeBoolean)) encodedTry
          case decodedTry of
            Nothing -> print "decoding failed"
            Just (d, _) -> if d == success then print "decoding succeeded"
                                           else print "values are inconsistent"
            


```
_You can find this program in the `main.hs` file_

You can compile this main file with GHC, using the usual

```
ghc main.hs
```

command, and then execute the program using

```
./main
```

The output should be :

```
"true : 0"
"false : 1"
"1"
Just (False,"")
"decoding succeeded"
"1110110"
"decoding succeeded"
"11110110"
"decoding succeeded"
```

Here is a table that recaps how those types are being serialised: 

| Term                         | Binary    |
|------------------------------|-----------|
| `False`                      | `1`       |
| `True`                       | `0`       |
| `[False, True, False]`       | `111010`  |
| `Right [False, True, False]` | `1111010` |


##### Footnote

We had to manually modify the generated Haskell file in order to fix some scoping issues and add a module header. 
See the related issues: 
[#171](https://github.com/typedefs/typedefs/issues/171) [#172](https://github.com/typedefs/typedefs/issues/172)
[#173](https://github.com/typedefs/typedefs/issues/173)


[INSTALL]: ../TUTORIAL_INSTALL.md
