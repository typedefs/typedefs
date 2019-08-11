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

