module Test.Haskell

import Names
import Typedefs

import Backend
import Backend.Utils
import Backend.Haskell

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.Vect
import Test

%access public export

generate : TNamed n -> Doc
generate = generateDefs Haskell

{-
boolForBit : SpecialiseEntry
boolForBit = MkSpecialiseEntry (def bit) "Bool"
                               "either (\\ () -> True) (\\ () -> False)"
                               "\\ x -> if x then Left () else Right ()"

charForByte : SpecialiseEntry
charForByte = MkSpecialiseEntry (def byte) "Char" "undefined" "undefined"

intForNat : SpecialiseEntry
intForNat = MkSpecialiseEntry (def nat) "Int"
                              "id"
                              "\\ x -> if x >= 0 then x else error \"negative number\""

generateSpecialised : Vect (S m) SpecialiseEntry -> TNamed n -> Doc
generateSpecialised se (TName nm td) = vsep2 $ map generateCode $ generateDefsSpecialised {lang=Haskell} se _ td
-}

x0 : Doc
x0 = text "x0"

x1 : Doc
x1 = text "x1"

x2 : Doc
x2 = text "x2"

x3 : Doc
x3 = text "x3"

testSuite : IO ()
testSuite = spec $ do

  describe "Haskell code generation tests:" $ do
    let bitDoc = text """type Bit = Either () ()

encodeBit :: Bit -> ByteString
encodeBit x = toLazyByteString (case x of
                                  Left z -> word8 (fromIntegral 0)
                                  Right z -> word8 (fromIntegral 1))

decodeBit :: ByteString -> (Maybe (Bit,ByteString))
decodeBit = runDeserializer (do
                               i <- deserializeInt
                               case i of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode)"""

    it "bit" $
      generate bit
        `shouldBe` vsep2 [ preamble {def = Haskell}, bitDoc ]


    let byteDoc = text """type Bit = Either () ()

type Byte = (Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit)

encodeByte :: Byte -> ByteString
encodeByte x = toLazyByteString (case x of
                                   (y
                                   ,y0
                                   ,y1
                                   ,y2
                                   ,y3
                                   ,y4
                                   ,y5
                                   ,y6) -> mconcat [(case y of
                                                       Left z -> word8 (fromIntegral 0)
                                                       Right z -> word8 (fromIntegral 1))
                                                   ,(case y0 of
                                                       Left z0 -> word8 (fromIntegral 0)
                                                       Right z0 -> word8 (fromIntegral 1))
                                                   ,(case y1 of
                                                       Left z1 -> word8 (fromIntegral 0)
                                                       Right z1 -> word8 (fromIntegral 1))
                                                   ,(case y2 of
                                                       Left z2 -> word8 (fromIntegral 0)
                                                       Right z2 -> word8 (fromIntegral 1))
                                                   ,(case y3 of
                                                       Left z3 -> word8 (fromIntegral 0)
                                                       Right z3 -> word8 (fromIntegral 1))
                                                   ,(case y4 of
                                                       Left z4 -> word8 (fromIntegral 0)
                                                       Right z4 -> word8 (fromIntegral 1))
                                                   ,(case y5 of
                                                       Left z5 -> word8 (fromIntegral 0)
                                                       Right z5 -> word8 (fromIntegral 1))
                                                   ,(case y6 of
                                                       Left z6 -> word8 (fromIntegral 0)
                                                       Right z6 -> word8 (fromIntegral 1))])

decodeByte :: ByteString -> (Maybe (Byte,ByteString))
decodeByte = runDeserializer (do
                                x <- do
                                       i <- deserializeInt
                                       case i of
                                         0 -> return (Left ())
                                         1 -> return (Right ())
                                         _ -> failDecode
                                x0 <- do
                                        i0 <- deserializeInt
                                        case i0 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x1 <- do
                                        i1 <- deserializeInt
                                        case i1 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x2 <- do
                                        i2 <- deserializeInt
                                        case i2 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x3 <- do
                                        i3 <- deserializeInt
                                        case i3 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x4 <- do
                                        i4 <- deserializeInt
                                        case i4 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x5 <- do
                                        i5 <- deserializeInt
                                        case i5 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                x6 <- do
                                        i6 <- deserializeInt
                                        case i6 of
                                          0 -> return (Left ())
                                          1 -> return (Right ())
                                          _ -> failDecode
                                return (x,x0,x1,x2,x3,x4,x5,x6))"""

    it "byte" $
      generate byte
        `shouldBe` vsep2 [ preamble {def = Haskell}, byteDoc ]

    it "maybe" $
      generate maybe
        `shouldBe` vsep2 [ preamble {def = Haskell}, text "type" |++| text "Maybe" |++| x0 |++| equals |++| text "Either" |++| parens empty |++| x0]

    let listDoc = text "data" |++| text "List" |++| x0
                  |++| equals |++| text "Nil"
                  |++| pipe   |++| text "Cons"
                                   |++| x0 |++| parens (text "List" |++| x0)

    it "list" $
      generate list `shouldBe` vsep2 [ preamble {def = Haskell}, listDoc]

    let muMaybeDoc = text "data" |++| text "Maybe2" |++| x0
                     |++| equals |++| text "Nothing"
                     |++| pipe   |++| text "Just" |++| x0

    it "maybe2" $
      generate maybe2 `shouldBe` vsep2 [ preamble {def = Haskell}, muMaybeDoc]

    let natDoc = text """data Nat = Z | S Nat

encodeNat :: Nat -> ByteString
encodeNat Z = toLazyByteString (word8 (fromIntegral 0))
encodeNat (S x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                            ,(encodeNat x)])

decodeNat :: Deserializer Nat
decodeNat = do
              i <- deserializeInt
              case i of
                0 -> return Z
                1 -> do
                       x <- decodeNat
                       return (S x)
                _ -> failDecode"""

    it "nat" $
      generate nat `shouldBe` vsep2 [ preamble {def = Haskell}, natDoc ]

    let listNatDoc = text """data Nat = Z | S Nat

data ListNat = NilN | ConsN Nat ListNat

encodeNat :: Nat -> ByteString
encodeNat Z = toLazyByteString (word8 (fromIntegral 0))
encodeNat (S x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                            ,(encodeNat x)])

encodeListNat :: ListNat -> ByteString
encodeListNat NilN = toLazyByteString (word8 (fromIntegral 0))
encodeListNat (ConsN x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                                    ,(case x of
                                                        (y
                                                        ,y0) -> mconcat [(encodeNat y)
                                                                        ,(encodeListNat y0)])])

decodeNat :: Deserializer Nat
decodeNat = do
              i <- deserializeInt
              case i of
                0 -> return Z
                1 -> do
                       x <- decodeNat
                       return (S x)
                _ -> failDecode

decodeListNat :: Deserializer ListNat
decodeListNat = do
                  i <- deserializeInt
                  case i of
                    0 -> return NilN
                    1 -> do
                           x1 <- do
                                   x <- decodeNat
                                   x0 <- decodeListNat
                                   return (x,x0)
                           return (ConsN x1)
                    _ -> failDecode"""

    it "listNat" $
      generate listNat
        `shouldBe` vsep2 [ preamble {def = Haskell}, listNatDoc ]


    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text "type" |++| text "Maybe" |++| x0 |++|
                                  equals |++| text "Either" |++| parens empty |++| x0
                    , text "type" |++| text "ParSyn" |++| x0 |++| equals |++| text "Maybe" |++| x0
                    ]

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text "data" |++| text "Maybe2" |++| x0 |++|
                                  equals |++| text "Nothing" |++|
                                  pipe   |++| text "Just" |++| x0
                    , text "type" |++| text "ParSyn2" |++| x0 |++| equals |++| text "Maybe2" |++| x0
                    ]

    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text "type" |++| text "Aplusbpluscplusd" |++| hsep [x0,x1,x2,x3] |++|
                                  equals |++| text "Either" |++| x0 |++|
                                                parens (text "Either" |++| x1 |++|
                                                  parens (text "Either" |++| text "x2" |++| text "x3"))
                    ]

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """type Oneoneoneone = Either () (Either () (Either () ()))

encodeOneoneoneone :: Oneoneoneone -> ByteString
encodeOneoneoneone x = toLazyByteString (case x of
                                           Left z -> word8 (fromIntegral 0)
                                           Right (Left z0) -> word8 (fromIntegral 1)
                                           Right (Right (Left z1)) -> word8 (fromIntegral 2)
                                           Right (Right (Right z1)) -> word8 (fromIntegral 3))

decodeOneoneoneone :: ByteString -> (Maybe (Oneoneoneone,ByteString))
decodeOneoneoneone = runDeserializer (do
                                        i <- deserializeInt
                                        case i of
                                          0 -> return (Left ())
                                          1 -> return (Right (Left ()))
                                          2 -> return (Right (Right (Left ())))
                                          3 -> return (Right (Right (Right ())))
                                          _ -> failDecode)"""
                    ]


    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text "type" |++| text "Id" |++| x0
                      |++| equals |++| x0 -- not "\ntype Id x0 x1 ... x42 = x0\n"
                    ]


    it "void or unit" $
      generate voidOrUnit
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """type VoidOrUnit = Either Void ()

encodeVoidOrUnit :: VoidOrUnit -> ByteString
encodeVoidOrUnit x = toLazyByteString (case x of
                                         Left z -> mconcat [(word8 (fromIntegral 0))
                                                           ,(absurd z)]
                                         Right z -> word8 (fromIntegral 1))

decodeVoidOrUnit :: ByteString -> (Maybe (VoidOrUnit,ByteString))
decodeVoidOrUnit = runDeserializer (do
                                      i <- deserializeInt
                                      case i of
                                        0 -> do
                                               y <- failDecode
                                               return (Left y)
                                        1 -> return (Right ())
                                        _ -> failDecode)"""
                    ]

    it "nonlinear variable usage" $
      generate nonlinear
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text "type" |++| text "Nonlinear" |++| x0
                      |++| equals |++| tupled [x0, x0]
                    ]

    let listAlphaOrBetaDoc =
      vsep2
        [ preamble {def = Haskell}
        , text """data List x0 = Nil | Cons x0 (List x0)

type ListAlphaOrBeta x0 x1 = List (Either x0 x1)"""
        ]

    it "listAlphaOrBeta" $
      generate listAlphaOrBeta `shouldBe` listAlphaOrBetaDoc

    it "listBitOrByte" $
      generate listBitOrByte
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """type Byte = (Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit)

type Bit = Either () ()

data List x0 = Nil | Cons x0 (List x0)

type ListAlphaOrBeta x0 x1 = List (Either x0 x1)

type ListBitOrByte = ListAlphaOrBeta Bit Byte

encodeListBitOrByte :: ListBitOrByte -> ByteString
encodeListBitOrByte Nil = toLazyByteString (word8 (fromIntegral 0))
encodeListBitOrByte (Cons x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                                   ,(case x of
                                                       (y
                                                       ,y0) -> mconcat [(case y of
                                                                           Left z -> mconcat [(word8 (fromIntegral 0))
                                                                                             ,(case z of
                                                                                                 Left z0 -> word8 (fromIntegral 0)
                                                                                                 Right z0 -> word8 (fromIntegral 1))]
                                                                           Right z -> mconcat [(word8 (fromIntegral 1))
                                                                                              ,(case z of
                                                                                                  (y1
                                                                                                  ,y2
                                                                                                  ,y3
                                                                                                  ,y4
                                                                                                  ,y5
                                                                                                  ,y6
                                                                                                  ,y7
                                                                                                  ,y8) -> mconcat [(case y1 of
                                                                                                                      Left z1 -> word8 (fromIntegral 0)
                                                                                                                      Right z1 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y2 of
                                                                                                                      Left z2 -> word8 (fromIntegral 0)
                                                                                                                      Right z2 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y3 of
                                                                                                                      Left z3 -> word8 (fromIntegral 0)
                                                                                                                      Right z3 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y4 of
                                                                                                                      Left z4 -> word8 (fromIntegral 0)
                                                                                                                      Right z4 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y5 of
                                                                                                                      Left z5 -> word8 (fromIntegral 0)
                                                                                                                      Right z5 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y6 of
                                                                                                                      Left z6 -> word8 (fromIntegral 0)
                                                                                                                      Right z6 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y7 of
                                                                                                                      Left z7 -> word8 (fromIntegral 0)
                                                                                                                      Right z7 -> word8 (fromIntegral 1))
                                                                                                                  ,(case y8 of
                                                                                                                      Left z8 -> word8 (fromIntegral 0)
                                                                                                                      Right z8 -> word8 (fromIntegral 1))])])
                                                                       ,(encodeListBitOrByte y0)])])

decodeListBitOrByte :: Deserializer ListBitOrByte
decodeListBitOrByte = do
                  i9 <- deserializeInt
                  case i9 of
                    0 -> return Nil
                    1 -> do
                           x9 <- do
                                   x <- do
                                          i8 <- deserializeInt
                                          case i8 of
                                            0 -> do
                                                   y1 <- do
                                                           i <- deserializeInt
                                                           case i of
                                                             0 -> return (Left ())
                                                             1 -> return (Right ())
                                                             _ -> failDecode
                                                   return (Left y1)
                                            1 -> do
                                                   y18 <- do
                                                            x1 <- do
                                                                    i0 <- deserializeInt
                                                                    case i0 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x2 <- do
                                                                    i1 <- deserializeInt
                                                                    case i1 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x3 <- do
                                                                    i2 <- deserializeInt
                                                                    case i2 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x4 <- do
                                                                    i3 <- deserializeInt
                                                                    case i3 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x5 <- do
                                                                    i4 <- deserializeInt
                                                                    case i4 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x6 <- do
                                                                    i5 <- deserializeInt
                                                                    case i5 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x7 <- do
                                                                    i6 <- deserializeInt
                                                                    case i6 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            x8 <- do
                                                                    i7 <- deserializeInt
                                                                    case i7 of
                                                                      0 -> return (Left ())
                                                                      1 -> return (Right ())
                                                                      _ -> failDecode
                                                            return (x1
                                                                   ,x2
                                                                   ,x3
                                                                   ,x4
                                                                   ,x5
                                                                   ,x6
                                                                   ,x7
                                                                   ,x8)
                                                   return (Right y18)
                                            _ -> failDecode
                                   x0 <- decodeListBitOrByte
                                   return (x,x0)
                           return (Cons x9)
                    _ -> failDecode"""
                    ]

    it "nested Mu 1: List(Either(Alpha, Beta))" $
      generate nestedMu1
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """data List x0 = Nil | Cons x0 (List x0)

data NestedMu1 x0 x1 = Foobar (List (Either x0 x1))"""
                    ]

    it "nested Mu 2: Maybe2(Alpha)" $
      generate nestedMu2
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """data Maybe2 x0 = Nothing | Just x0

data NestedMu2 x0 = Foobar (Maybe2 x0)"""
                    ]

{- TODO
    it "nested Mu 3: Maybe2(Mu)" $
      generate nestedMu3
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """data Maybe2 x0 = Nothing | Just x0

data NestedMu3 = Foobar (Maybe2 NestedMu3)

encodeMaybe2 :: Maybe2 -> ByteString
encodeMaybe2 Nothing = toLazyByteString (word8 (fromIntegral 0))
encodeMaybe2 (Just x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                                  ,(encodeFoobar x)])

encodeNestedMu3 :: NestedMu3 -> ByteString
encodeNestedMu3 (Foobar x) = toLazyByteString (mconcat [(word8 (fromIntegral 0))
                                                       ,(encodeMaybe2 x)])

decodeMaybe2 :: Deserializer Maybe2
decodeMaybe2 = do
                 i <- deserializeInt
                 case i of
                   0 -> return Nothing
                   1 -> do
                          x <- decodeFoobar
                          return (Just x)
                   _ -> failDecode

decodeNestedMu3 :: Deserializer NestedMu3
decodeNestedMu3 = do
                    i <- deserializeInt
                    case i of
                      0 -> do
                             x <- decodeMaybe2
                             return (Foobar x)
                      _ -> failDecode"""
                    ]
-}

    it "nested mu 4: List(Either (Mu, Alpha))" $
      generate nestedMu4 `shouldBe`
                   vsep2
                    [ preamble {def = Haskell}
                    , text """data List x0 = Nil | Cons x0 (List x0)

data NestedMu4 x0 = Foobar (List (Either (NestedMu4 x0) x0))"""
                    ]
{- TODO
    it "nested mu 5: AnonList(Mu)" $
      generate nestedMu5
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """data NilCons x0 = Nil | Cons x0 (NilCons x0)

data NestedMu5 = Foobar (NilCons NestedMu5)

encodeNilCons :: NilCons -> ByteString
encodeNilCons Nil = toLazyByteString (word8 (fromIntegral 0))
encodeNilCons (Cons x) = toLazyByteString (mconcat [(word8 (fromIntegral 1))
                                                   ,(case x of
                                                       (y
                                                       ,y0) -> mconcat [(encodeFoobar y)
                                                                       ,(encodeNilCons y0)])])

encodeNestedMu5 :: NestedMu5 -> ByteString
encodeNestedMu5 (Foobar x) = toLazyByteString (mconcat [(word8 (fromIntegral 0))
                                                       ,(encodeMuNilCons x)])

decodeNilCons :: Deserializer NilCons
decodeNilCons = do
                  i <- deserializeInt
                  case i of
                    0 -> return Nil
                    1 -> do
                           x1 <- do
                                   x <- decodeFoobar
                                   x0 <- decodeNilCons
                                   return (x,x0)
                           return (Cons x1)
                    _ -> failDecode

decodeNestedMu5 :: Deserializer NestedMu5
decodeNestedMu5 = do
                    i <- deserializeInt
                    case i of
                      0 -> do
                             x <- decodeMuNilCons
                             return (Foobar x)
                      _ -> failDecode"""
                    ]


    it "nested Mu 6: NestedMu4(Maybe2(Either(Alpha, Nat)))" $
      generate nestedMu6
        `shouldBe` vsep2
                    [ preamble {def = Haskell}
                    , text """"""
                    ]
-}

{-
  describe "Haskell specialised types tests:" $ do

    let boolForBitDoc = text "type" |++| text "Byte"
                        |++| equals |++| tupled (replicate 8 $ text "Bool")

    it "bit" $
      generateSpecialised [boolForBit] byte
        `shouldBe` boolForBitDoc

    it "byte" $
      generateSpecialised [charForByte, boolForBit] listByte
        `shouldBe` text "data" |++| text "ListByte"
                      |++| equals |++| text "NilC"
                      |++| pipe   |++| text "ConsC" |++| text "Char" |++| text "ListByte"

    it "byteWrongOrder" $
      generateSpecialised [boolForBit, charForByte] listByte
        `shouldBe` vsep2
                        [ boolForBitDoc
                        , text "data" |++| text "ListByte"
                          |++| equals |++| text "NilC"
                          |++| pipe   |++| text "ConsC" |++| text "Byte" |++| text "ListByte"
                        ]

    it "triple with Byte |-> Char, Listnat, Alpha" $
      generateSpecialised [charForByte, boolForBit, intForNat] tripleByteListnatAlpha
        `shouldBe` vsep2
                        [ text "data" |++| text "ListNat"
                          |++| equals |++| text "NilN"
                          |++| pipe   |++| text "ConsN" |++| text "Int" |++| text "ListNat"
                        , text "type" |++| text "Triple" |++| x0
                          |++| equals |++| tupled [text "Char", text "ListNat", x0]
                        ]
-}
