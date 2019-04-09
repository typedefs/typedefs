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

encodeBit :: Serialiser Bit
encodeBit x = case x of
                Left z -> word8 (fromIntegral 0)
                Right z -> word8 (fromIntegral 1)

decodeBit :: Deserialiser Bit
decodeBit = do
              i <- deserialiseInt
              case i of
                0 -> return (Left ())
                1 -> return (Right ())
                _ -> failDecode"""

    it "bit" $
      generate bit
        `shouldBe` vsep2 [ preamble {def = Haskell}, bitDoc ]


    let byteDoc = text """type Bit = Either () ()

type Byte = (Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit)

encodeBit :: Serialiser Bit
encodeBit x = case x of
                Left z -> word8 (fromIntegral 0)
                Right z -> word8 (fromIntegral 1)

decodeBit :: Deserialiser Bit
decodeBit = do
              i <- deserialiseInt
              case i of
                0 -> return (Left ())
                1 -> return (Right ())
                _ -> failDecode

encodeByte :: Serialiser Byte
encodeByte x = case x of
                 (y,y0,y1,y2,y3,y4,y5,y6) -> mconcat [(encodeBit y)
                                                     ,(encodeBit y0)
                                                     ,(encodeBit y1)
                                                     ,(encodeBit y2)
                                                     ,(encodeBit y3)
                                                     ,(encodeBit y4)
                                                     ,(encodeBit y5)
                                                     ,(encodeBit y6)]

decodeByte :: Deserialiser Byte
decodeByte = do
               x <- decodeBit
               x0 <- decodeBit
               x1 <- decodeBit
               x2 <- decodeBit
               x3 <- decodeBit
               x4 <- decodeBit
               x5 <- decodeBit
               x6 <- decodeBit
               return (x,x0,x1,x2,x3,x4,x5,x6)"""

    it "byte" $
      generate byte
        `shouldBe` vsep2 [ preamble {def = Haskell}, byteDoc ]

    let maybeDoc = text """type Maybe x0 = Either () x0

encodeMaybe :: Serialiser x0 -> Serialiser (Maybe x0)
encodeMaybe encodeX0 x = case x of
                           Left z -> word8 (fromIntegral 0)
                           Right z -> mconcat [(word8 (fromIntegral 1))
                                              ,(encodeX0 z)]

decodeMaybe :: Deserialiser x0 -> Deserialiser (Maybe x0)
decodeMaybe decodeX0 = do
                         i <- deserialiseInt
                         case i of
                           0 -> return (Left ())
                           1 -> do
                                  y0 <- decodeX0
                                  return (Right y0)
                           _ -> failDecode"""

    it "maybe" $
      generate maybe
        `shouldBe` vsep2 [ preamble {def = Haskell}, maybeDoc ]

    let listDoc = text """data List x0 = Nil | Cons x0 (List x0)

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode"""

    it "list" $
      generate list `shouldBe` vsep2 [ preamble {def = Haskell}, listDoc]

    let muMaybeDoc = text """data Maybe2 x0 = Nothing | Just x0

encodeMaybe2 :: Serialiser x0 -> Serialiser (Maybe2 x0)
encodeMaybe2 encodeX0 Nothing = word8 (fromIntegral 0)
encodeMaybe2 encodeX0 (Just x) = mconcat [(word8 (fromIntegral 1)),(encodeX0 x)]

decodeMaybe2 :: Deserialiser x0 -> Deserialiser (Maybe2 x0)
decodeMaybe2 decodeX0 = do
                          i <- deserialiseInt
                          case i of
                            0 -> return Nothing
                            1 -> do
                                   x <- decodeX0
                                   return (Just x)
                            _ -> failDecode"""

    it "maybe2" $
      generate maybe2 `shouldBe` vsep2 [ preamble {def = Haskell}, muMaybeDoc]

    let natDoc = text """data Nat = Z | S Nat

encodeNat :: Serialiser Nat
encodeNat Z = word8 (fromIntegral 0)
encodeNat (S x) = mconcat [(word8 (fromIntegral 1)),(encodeNat x)]

decodeNat :: Deserialiser Nat
decodeNat = do
              i <- deserialiseInt
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

encodeNat :: Serialiser Nat
encodeNat Z = word8 (fromIntegral 0)
encodeNat (S x) = mconcat [(word8 (fromIntegral 1)),(encodeNat x)]

decodeNat :: Deserialiser Nat
decodeNat = do
              i <- deserialiseInt
              case i of
                0 -> return Z
                1 -> do
                       x <- decodeNat
                       return (S x)
                _ -> failDecode

encodeListNat :: Serialiser ListNat
encodeListNat NilN = word8 (fromIntegral 0)
encodeListNat (ConsN x x0) = mconcat [(word8 (fromIntegral 1))
                                     ,(encodeNat x)
                                     ,(encodeListNat x0)]

decodeListNat :: Deserialiser ListNat
decodeListNat = do
                  i <- deserialiseInt
                  case i of
                    0 -> return NilN
                    1 -> do
                           x <- decodeNat
                           x0 <- decodeListNat
                           return (ConsN x x0)
                    _ -> failDecode"""

    it "listNat" $
      generate listNat
        `shouldBe` vsep2 [ preamble {def = Haskell}, listNatDoc ]

    let parametricDoc = text """type Maybe x0 = Either () x0

type ParSyn x0 = Maybe x0

encodeMaybe :: Serialiser x0 -> Serialiser (Maybe x0)
encodeMaybe encodeX0 x = case x of
                           Left z -> word8 (fromIntegral 0)
                           Right z -> mconcat [(word8 (fromIntegral 1))
                                              ,(encodeX0 z)]

decodeMaybe :: Deserialiser x0 -> Deserialiser (Maybe x0)
decodeMaybe decodeX0 = do
                         i <- deserialiseInt
                         case i of
                           0 -> return (Left ())
                           1 -> do
                                  y0 <- decodeX0
                                  return (Right y0)
                           _ -> failDecode

encodeParSyn :: Serialiser x0 -> Serialiser (ParSyn x0)
encodeParSyn encodeX0 x = encodeMaybe encodeX0 x

decodeParSyn :: Deserialiser x0 -> Deserialiser (ParSyn x0)
decodeParSyn decodeX0 = decodeMaybe decodeX0"""

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, parametricDoc ]

    let parametric2Doc = text """data Maybe2 x0 = Nothing | Just x0

type ParSyn2 x0 = Maybe2 x0

encodeMaybe2 :: Serialiser x0 -> Serialiser (Maybe2 x0)
encodeMaybe2 encodeX0 Nothing = word8 (fromIntegral 0)
encodeMaybe2 encodeX0 (Just x) = mconcat [(word8 (fromIntegral 1)),(encodeX0 x)]

decodeMaybe2 :: Deserialiser x0 -> Deserialiser (Maybe2 x0)
decodeMaybe2 decodeX0 = do
                          i <- deserialiseInt
                          case i of
                            0 -> return Nothing
                            1 -> do
                                   x <- decodeX0
                                   return (Just x)
                            _ -> failDecode

encodeParSyn2 :: Serialiser x0 -> Serialiser (ParSyn2 x0)
encodeParSyn2 encodeX0 x = encodeMaybe2 encodeX0 x

decodeParSyn2 :: Deserialiser x0 -> Deserialiser (ParSyn2 x0)
decodeParSyn2 decodeX0 = decodeMaybe2 decodeX0"""

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, parametric2Doc ]

    let aplusbpluscplusdDoc = text """type Aplusbpluscplusd x0 x1 x2 x3 = Either x0 (Either x1 (Either x2 x3))

encodeAplusbpluscplusd :: Serialiser x0 -> Serialiser x1 -> Serialiser x2 -> Serialiser x3 -> Serialiser (Aplusbpluscplusd x0 x1 x2 x3)
encodeAplusbpluscplusd encodeX0 encodeX1 encodeX2 encodeX3 x = case x of
                                                                 Left z -> mconcat [(word8 (fromIntegral 0))
                                                                                   ,(encodeX0 z)]
                                                                 Right (Left z0) -> mconcat [(word8 (fromIntegral 1))
                                                                                            ,(encodeX1 z0)]
                                                                 Right (Right (Left z1)) -> mconcat [(word8 (fromIntegral 2))
                                                                                                    ,(encodeX2 z1)]
                                                                 Right (Right (Right z1)) -> mconcat [(word8 (fromIntegral 3))
                                                                                                     ,(encodeX3 z1)]

decodeAplusbpluscplusd :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser x2 -> Deserialiser x3 -> Deserialiser (Aplusbpluscplusd x0 x1 x2 x3)
decodeAplusbpluscplusd decodeX0 decodeX1 decodeX2 decodeX3 = do
                                                               i <- deserialiseInt
                                                               case i of
                                                                 0 -> do
                                                                        y <- decodeX0
                                                                        return (Left y)
                                                                 1 -> do
                                                                        y0 <- decodeX1
                                                                        return (Right (Left y0))
                                                                 2 -> do
                                                                        y1 <- decodeX2
                                                                        return (Right (Right (Left y1)))
                                                                 3 -> do
                                                                        y2 <- decodeX3
                                                                        return (Right (Right (Right y2)))
                                                                 _ -> failDecode"""

    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, aplusbpluscplusdDoc ]

    let oneoneoneoneDoc = text """type Oneoneoneone = Either () (Either () (Either () ()))

encodeOneoneoneone :: Serialiser Oneoneoneone
encodeOneoneoneone x = case x of
                         Left z -> word8 (fromIntegral 0)
                         Right (Left z0) -> word8 (fromIntegral 1)
                         Right (Right (Left z1)) -> word8 (fromIntegral 2)
                         Right (Right (Right z1)) -> word8 (fromIntegral 3)

decodeOneoneoneone :: Deserialiser Oneoneoneone
decodeOneoneoneone = do
                       i <- deserialiseInt
                       case i of
                         0 -> return (Left ())
                         1 -> return (Right (Left ()))
                         2 -> return (Right (Right (Left ())))
                         3 -> return (Right (Right (Right ())))
                         _ -> failDecode"""

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, oneoneoneoneDoc ]

    let unusedFreeVarsDoc = text """type Id x0 = x0

encodeId :: Serialiser x0 -> Serialiser (Id x0)
encodeId encodeX0 x = encodeX0 x

decodeId :: Deserialiser x0 -> Deserialiser (Id x0)
decodeId decodeX0 = decodeX0"""

    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, unusedFreeVarsDoc ]

    let voidOrUnitDoc = text """type VoidOrUnit = Either Void ()

encodeVoidOrUnit :: Serialiser VoidOrUnit
encodeVoidOrUnit x = case x of
                       Left z -> mconcat [(word8 (fromIntegral 0)),(absurd z)]
                       Right z -> word8 (fromIntegral 1)

decodeVoidOrUnit :: Deserialiser VoidOrUnit
decodeVoidOrUnit = do
                     i <- deserialiseInt
                     case i of
                       0 -> do
                              y <- failDecode
                              return (Left y)
                       1 -> return (Right ())
                       _ -> failDecode"""

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, voidOrUnitDoc ]

    let nonlinearDoc = text """type Nonlinear x0 = (x0,x0)

encodeNonlinear :: Serialiser x0 -> Serialiser (Nonlinear x0)
encodeNonlinear encodeX0 x = case x of
                               (y,y0) -> mconcat [(encodeX0 y),(encodeX0 y0)]

decodeNonlinear :: Deserialiser x0 -> Deserialiser (Nonlinear x0)
decodeNonlinear decodeX0 = do
                             x <- decodeX0
                             x0 <- decodeX0
                             return (x,x0)"""

    it "nonlinear variable usage" $
      generate nonlinear
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nonlinearDoc ]

    let listAlphaOrBetaDoc = text """data List x0 = Nil | Cons x0 (List x0)

type ListAlphaOrBeta x0 x1 = List (Either x0 x1)

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode

encodeSumx0x1 :: Serialiser x0 -> Serialiser x1 -> Serialiser (Either x0 x1)
encodeSumx0x1 encodeX0 encodeX1 x = case x of
                                      Left z -> mconcat [(word8 (fromIntegral 0))
                                                        ,(encodeX0 z)]
                                      Right z -> mconcat [(word8 (fromIntegral 1))
                                                         ,(encodeX1 z)]

decodeSumx0x1 :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (Either x0 x1)
decodeSumx0x1 decodeX0 decodeX1 = do
                                    i <- deserialiseInt
                                    case i of
                                      0 -> do
                                             y <- decodeX0
                                             return (Left y)
                                      1 -> do
                                             y0 <- decodeX1
                                             return (Right y0)
                                      _ -> failDecode

encodeListAlphaOrBeta :: Serialiser x0 -> Serialiser x1 -> Serialiser (ListAlphaOrBeta x0 x1)
encodeListAlphaOrBeta encodeX0 encodeX1 x = encodeList (encodeSumx0x1 encodeX0 encodeX1) x

decodeListAlphaOrBeta :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (ListAlphaOrBeta x0 x1)
decodeListAlphaOrBeta decodeX0 decodeX1 = decodeList (decodeSumx0x1 decodeX0 decodeX1)"""

    it "listAlphaOrBeta" $
      generate listAlphaOrBeta
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, listAlphaOrBetaDoc ]

    let listBitOrByteDoc = text """type Byte = (Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit)

type Bit = Either () ()

data List x0 = Nil | Cons x0 (List x0)

type ListAlphaOrBeta x0 x1 = List (Either x0 x1)

type ListBitOrByte = ListAlphaOrBeta Bit Byte

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode

encodeSumx0x1 :: Serialiser x0 -> Serialiser x1 -> Serialiser (Either x0 x1)
encodeSumx0x1 encodeX0 encodeX1 x = case x of
                                      Left z -> mconcat [(word8 (fromIntegral 0))
                                                        ,(encodeX0 z)]
                                      Right z -> mconcat [(word8 (fromIntegral 1))
                                                         ,(encodeX1 z)]

decodeSumx0x1 :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (Either x0 x1)
decodeSumx0x1 decodeX0 decodeX1 = do
                                    i <- deserialiseInt
                                    case i of
                                      0 -> do
                                             y <- decodeX0
                                             return (Left y)
                                      1 -> do
                                             y0 <- decodeX1
                                             return (Right y0)
                                      _ -> failDecode

encodeListAlphaOrBeta :: Serialiser x0 -> Serialiser x1 -> Serialiser (ListAlphaOrBeta x0 x1)
encodeListAlphaOrBeta encodeX0 encodeX1 x = encodeList (encodeSumx0x1 encodeX0 encodeX1) x

decodeListAlphaOrBeta :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (ListAlphaOrBeta x0 x1)
decodeListAlphaOrBeta decodeX0 decodeX1 = decodeList (decodeSumx0x1 decodeX0 decodeX1)

encodeBit :: Serialiser Bit
encodeBit x = case x of
                Left z -> word8 (fromIntegral 0)
                Right z -> word8 (fromIntegral 1)

decodeBit :: Deserialiser Bit
decodeBit = do
              i <- deserialiseInt
              case i of
                0 -> return (Left ())
                1 -> return (Right ())
                _ -> failDecode

encodeByte :: Serialiser Byte
encodeByte x = case x of
                 (y,y0,y1,y2,y3,y4,y5,y6) -> mconcat [(encodeBit y)
                                                     ,(encodeBit y0)
                                                     ,(encodeBit y1)
                                                     ,(encodeBit y2)
                                                     ,(encodeBit y3)
                                                     ,(encodeBit y4)
                                                     ,(encodeBit y5)
                                                     ,(encodeBit y6)]

decodeByte :: Deserialiser Byte
decodeByte = do
               x <- decodeBit
               x0 <- decodeBit
               x1 <- decodeBit
               x2 <- decodeBit
               x3 <- decodeBit
               x4 <- decodeBit
               x5 <- decodeBit
               x6 <- decodeBit
               return (x,x0,x1,x2,x3,x4,x5,x6)

encodeListBitOrByte :: Serialiser ListBitOrByte
encodeListBitOrByte x = encodeListAlphaOrBeta encodeBit encodeByte x

decodeListBitOrByte :: Deserialiser ListBitOrByte
decodeListBitOrByte = decodeListAlphaOrBeta decodeBit decodeByte"""

    it "listBitOrByte" $
      generate listBitOrByte
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, listBitOrByteDoc ]

    let nestedMu1Doc = text """data List x0 = Nil | Cons x0 (List x0)

data NestedMu1 x0 x1 = Foobar (List (Either x0 x1))

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode

encodeSumx1x2 :: Serialiser x1 -> Serialiser x2 -> Serialiser (Either x1 x2)
encodeSumx1x2 encodeX1 encodeX2 x = case x of
                                      Left z -> mconcat [(word8 (fromIntegral 0))
                                                        ,(encodeX1 z)]
                                      Right z -> mconcat [(word8 (fromIntegral 1))
                                                         ,(encodeX2 z)]

decodeSumx1x2 :: Deserialiser x1 -> Deserialiser x2 -> Deserialiser (Either x1 x2)
decodeSumx1x2 decodeX1 decodeX2 = do
                                    i <- deserialiseInt
                                    case i of
                                      0 -> do
                                             y <- decodeX1
                                             return (Left y)
                                      1 -> do
                                             y0 <- decodeX2
                                             return (Right y0)
                                      _ -> failDecode

encodeNestedMu1 :: Serialiser x0 -> Serialiser x1 -> Serialiser (NestedMu1 x0 x1)
encodeNestedMu1 encodeX0 encodeX1 (Foobar x) = encodeList (encodeSumx1x2 encodeX0 encodeX1) x

decodeNestedMu1 :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (NestedMu1 x0 x1)
decodeNestedMu1 decodeX0 decodeX1 = do
                                      x <- decodeList (decodeSumx1x2 decodeX0 decodeX1)
                                      return (Foobar x)"""

    it "nested Mu 1: List(Either(Alpha, Beta))" $
      generate nestedMu1
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nestedMu1Doc ]

    let nestedMu2Doc = text """data Maybe2 x0 = Nothing | Just x0

data NestedMu2 x0 = Foobar (Maybe2 x0)

encodeMaybe2 :: Serialiser x0 -> Serialiser (Maybe2 x0)
encodeMaybe2 encodeX0 Nothing = word8 (fromIntegral 0)
encodeMaybe2 encodeX0 (Just x) = mconcat [(word8 (fromIntegral 1)),(encodeX0 x)]

decodeMaybe2 :: Deserialiser x0 -> Deserialiser (Maybe2 x0)
decodeMaybe2 decodeX0 = do
                          i <- deserialiseInt
                          case i of
                            0 -> return Nothing
                            1 -> do
                                   x <- decodeX0
                                   return (Just x)
                            _ -> failDecode

encodeNestedMu2 :: Serialiser x0 -> Serialiser (NestedMu2 x0)
encodeNestedMu2 encodeX0 (Foobar x) = encodeMaybe2 encodeX0 x

decodeNestedMu2 :: Deserialiser x0 -> Deserialiser (NestedMu2 x0)
decodeNestedMu2 decodeX0 = do
                             x <- decodeMaybe2 decodeX0
                             return (Foobar x)"""

    it "nested Mu 2: Maybe2(Alpha)" $
      generate nestedMu2
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nestedMu2Doc ]

    let nestedMu3Doc = text """data Maybe2 x0 = Nothing | Just x0

data NestedMu3 = Foobar (Maybe2 NestedMu3)

encodeMaybe2 :: Serialiser x0 -> Serialiser (Maybe2 x0)
encodeMaybe2 encodeX0 Nothing = word8 (fromIntegral 0)
encodeMaybe2 encodeX0 (Just x) = mconcat [(word8 (fromIntegral 1)),(encodeX0 x)]

decodeMaybe2 :: Deserialiser x0 -> Deserialiser (Maybe2 x0)
decodeMaybe2 decodeX0 = do
                          i <- deserialiseInt
                          case i of
                            0 -> return Nothing
                            1 -> do
                                   x <- decodeX0
                                   return (Just x)
                            _ -> failDecode

encodeNestedMu3 :: Serialiser NestedMu3
encodeNestedMu3 (Foobar x) = encodeMaybe2 encodeNestedMu3 x

decodeNestedMu3 :: Deserialiser NestedMu3
decodeNestedMu3 = do
                    x <- decodeMaybe2 decodeNestedMu3
                    return (Foobar x)"""

    it "nested Mu 3: Maybe2(Mu)" $
      generate nestedMu3
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nestedMu3Doc ]

    let nestedMu4Doc = text """data List x0 = Nil | Cons x0 (List x0)

data NestedMu4 x0 = Foobar (List (Either (NestedMu4 x0) x0))

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode

encodeSumx0x1 :: Serialiser x0 -> Serialiser x1 -> Serialiser (Either x0 x1)
encodeSumx0x1 encodeX0 encodeX1 x = case x of
                                      Left z -> mconcat [(word8 (fromIntegral 0))
                                                        ,(encodeX0 z)]
                                      Right z -> mconcat [(word8 (fromIntegral 1))
                                                         ,(encodeX1 z)]

decodeSumx0x1 :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (Either x0 x1)
decodeSumx0x1 decodeX0 decodeX1 = do
                                    i <- deserialiseInt
                                    case i of
                                      0 -> do
                                             y <- decodeX0
                                             return (Left y)
                                      1 -> do
                                             y0 <- decodeX1
                                             return (Right y0)
                                      _ -> failDecode

encodeNestedMu4 :: Serialiser x0 -> Serialiser (NestedMu4 x0)
encodeNestedMu4 encodeX0 (Foobar x) = encodeList (encodeSumx0x1 (encodeNestedMu4 encodeX0) encodeX0) x

decodeNestedMu4 :: Deserialiser x0 -> Deserialiser (NestedMu4 x0)
decodeNestedMu4 decodeX0 = do
                             x <- decodeList (decodeSumx0x1 (decodeNestedMu4 decodeX0) decodeX0)
                             return (Foobar x)"""

    it "nested mu 4: List(Either (Mu, Alpha))" $
      generate nestedMu4
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nestedMu4Doc ]

    let nestedMu5Doc = text """data NilCons x0 = Nil | Cons x0 (NilCons x0)

data NestedMu5 = Foobar (NilCons NestedMu5)

encodeNilCons :: Serialiser x0 -> Serialiser (NilCons x0)
encodeNilCons encodeX0 Nil = word8 (fromIntegral 0)
encodeNilCons encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                             ,(encodeX0 x)
                                             ,(encodeNilCons encodeX0 x0)]

decodeNilCons :: Deserialiser x0 -> Deserialiser (NilCons x0)
decodeNilCons decodeX0 = do
                           i <- deserialiseInt
                           case i of
                             0 -> return Nil
                             1 -> do
                                    x <- decodeX0
                                    x0 <- decodeNilCons decodeX0
                                    return (Cons x x0)
                             _ -> failDecode

encodeNestedMu5 :: Serialiser NestedMu5
encodeNestedMu5 (Foobar x) = encodeNilCons encodeNestedMu5 x

decodeNestedMu5 :: Deserialiser NestedMu5
decodeNestedMu5 = do
                    x <- decodeNilCons decodeNestedMu5
                    return (Foobar x)"""

    it "nested mu 5: AnonList(Mu)" $
      generate nestedMu5
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, nestedMu5Doc ]

    let singleConstructorMuDoc = text """data List x0 = Nil | Cons x0 (List x0)

data Foo = Bar (List Foo) (Either () Foo)

encodeList :: Serialiser x0 -> Serialiser (List x0)
encodeList encodeX0 Nil = word8 (fromIntegral 0)
encodeList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                          ,(encodeX0 x)
                                          ,(encodeList encodeX0 x0)]

decodeList :: Deserialiser x0 -> Deserialiser (List x0)
decodeList decodeX0 = do
                        i <- deserialiseInt
                        case i of
                          0 -> return Nil
                          1 -> do
                                 x <- decodeX0
                                 x0 <- decodeList decodeX0
                                 return (Cons x x0)
                          _ -> failDecode

encodeFoo :: Serialiser Foo
encodeFoo (Bar x x0) = mconcat [(encodeList encodeFoo x)
                               ,(case x0 of
                                   Left z -> word8 (fromIntegral 0)
                                   Right z -> mconcat [(word8 (fromIntegral 1))
                                                      ,(encodeFoo z)])]

decodeFoo :: Deserialiser Foo
decodeFoo = do
              x <- decodeList decodeFoo
              x0 <- do
                      i <- deserialiseInt
                      case i of
                        0 -> return (Left ())
                        1 -> do
                               y0 <- decodeFoo
                               return (Right y0)
                        _ -> failDecode
              return (Bar x x0)"""

    it "single constructor mu" $
      generate singleConstructorMu
        `shouldBe` vsep2
                    [ preamble {def = Haskell}, singleConstructorMuDoc ]

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
