module Typedefs.Test.HaskellStrings

import Text.PrettyPrint.WL

%access export

bitDoc : Doc
bitDoc = text """type Bit = Either () ()

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

byteDoc : Doc
byteDoc = text """type Bit = Either () ()

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

maybeDoc : Doc
maybeDoc = text """type Maybe x0 = Either () x0

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

listDoc : Doc
listDoc = text """data List x0 = Nil | Cons x0 (List x0)

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

muMaybeDoc : Doc
muMaybeDoc = text """data Maybe2 x0 = Nothing | Just x0

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

natDoc : Doc
natDoc = text """data Nat = Z | S Nat

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

listNatDoc : Doc
listNatDoc = text """data Nat = Z | S Nat

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

parametricDoc : Doc
parametricDoc = text """type Maybe x0 = Either () x0

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

parametric2Doc : Doc
parametric2Doc = text """data Maybe2 x0 = Nothing | Just x0

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

aplusbpluscplusdDoc : Doc
aplusbpluscplusdDoc = text """type Aplusbpluscplusd x0 x1 x2 x3 = Either x0 (Either x1 (Either x2 x3))

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


oneoneoneoneDoc : Doc
oneoneoneoneDoc = text """type Oneoneoneone = Either () (Either () (Either () ()))

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

unusedFreeVarsDoc : Doc
unusedFreeVarsDoc = text """type Id x0 = x0

encodeId :: Serialiser x0 -> Serialiser (Id x0)
encodeId encodeX0 x = encodeX0 x

decodeId :: Deserialiser x0 -> Deserialiser (Id x0)
decodeId decodeX0 = decodeX0"""

voidOrUnitDoc : Doc
voidOrUnitDoc = text """type VoidOrUnit = Either Void ()

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
nonlinearDoc : Doc
nonlinearDoc = text """type Nonlinear x0 = (x0,x0)

encodeNonlinear :: Serialiser x0 -> Serialiser (Nonlinear x0)
encodeNonlinear encodeX0 x = case x of
                               (y,y0) -> mconcat [(encodeX0 y),(encodeX0 y0)]

decodeNonlinear :: Deserialiser x0 -> Deserialiser (Nonlinear x0)
decodeNonlinear decodeX0 = do
                             x <- decodeX0
                             x0 <- decodeX0
                             return (x,x0)"""

listAlphaOrBetaDoc : Doc
listAlphaOrBetaDoc = text """data List x0 = Nil | Cons x0 (List x0)

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

listBitOrByteDoc : Doc
listBitOrByteDoc = text """data List x0 = Nil | Cons x0 (List x0)

type ListAlphaOrBeta x0 x1 = List (Either x0 x1)

type Bit = Either () ()

type Byte = (Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit)

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

nestedMu1Doc : Doc
nestedMu1Doc = text """data List x0 = Nil | Cons x0 (List x0)

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
nestedMu2Doc : Doc
nestedMu2Doc = text """data Maybe2 x0 = Nothing | Just x0

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

nestedMu3Doc : Doc
nestedMu3Doc = text """data Maybe2 x0 = Nothing | Just x0

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

nestedMu4Doc : Doc
nestedMu4Doc = text """data List x0 = Nil | Cons x0 (List x0)

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

nestedMu5Doc : Doc
nestedMu5Doc = text """data NilCons x0 = Nil | Cons x0 (NilCons x0)

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

singleConstructorMuDoc : Doc
singleConstructorMuDoc = text """data List x0 = Nil | Cons x0 (List x0)

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

listOfDefsDoc : Doc 
listOfDefsDoc = text """type Bit = Either () ()

type Nibble = (Bit,Bit,Bit,Bit)

type Byte = (Nibble,Nibble)

type Char = Byte

type Hash = Byte

type TransitionId = Byte

type Data = Byte

type Previous = Hash

type RootTx = (Data,Previous)

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

encodeNibble :: Serialiser Nibble
encodeNibble x = case x of
                   (y,y0,y1,y2) -> mconcat [(encodeBit y)
                                           ,(encodeBit y0)
                                           ,(encodeBit y1)
                                           ,(encodeBit y2)]

decodeNibble :: Deserialiser Nibble
decodeNibble = do
                 x <- decodeBit
                 x0 <- decodeBit
                 x1 <- decodeBit
                 x2 <- decodeBit
                 return (x,x0,x1,x2)

encodeByte :: Serialiser Byte
encodeByte x = case x of
                 (y,y0) -> mconcat [(encodeNibble y),(encodeNibble y0)]

decodeByte :: Deserialiser Byte
decodeByte = do
               x <- decodeNibble
               x0 <- decodeNibble
               return (x,x0)

encodeChar :: Serialiser Char
encodeChar x = encodeByte x

decodeChar :: Deserialiser Char
decodeChar = decodeByte

encodeHash :: Serialiser Hash
encodeHash x = encodeByte x

decodeHash :: Deserialiser Hash
decodeHash = decodeByte

encodeTransitionId :: Serialiser TransitionId
encodeTransitionId x = encodeByte x

decodeTransitionId :: Deserialiser TransitionId
decodeTransitionId = decodeByte

encodeData :: Serialiser Data
encodeData x = encodeByte x

decodeData :: Deserialiser Data
decodeData = decodeByte

encodePrevious :: Serialiser Previous
encodePrevious x = encodeHash x

decodePrevious :: Deserialiser Previous
decodePrevious = decodeHash

encodeRootTx :: Serialiser RootTx
encodeRootTx x = case x of
                   (y,y0) -> mconcat [(encodeData y),(encodePrevious y0)]

decodeRootTx :: Deserialiser RootTx
decodeRootTx = do
                 x <- decodeData
                 x0 <- decodePrevious
                 return (x,x0)"""

largeTupleDoc : Doc
largeTupleDoc = text """type LargeTuple = (Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,Either () ()
                  ,(Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,Either () ()
                   ,(Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,Either () ()
                    ,(Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()
                     ,Either () ()))))

encodeLargeTuple :: Serialiser LargeTuple
encodeLargeTuple x = case x of
                       (y
                       ,y0
                       ,y1
                       ,y2
                       ,y3
                       ,y4
                       ,y5
                       ,y6
                       ,y7
                       ,y8
                       ,y9
                       ,y10
                       ,y11
                       ,y12
                       ,y13
                       ,y14
                       ,y15
                       ,y16
                       ,y17
                       ,y18
                       ,y19
                       ,y20
                       ,y21
                       ,y22
                       ,y23
                       ,y24
                       ,y25
                       ,y26
                       ,y27
                       ,y28
                       ,y29
                       ,y30
                       ,y31
                       ,y32
                       ,y33
                       ,y34
                       ,y35
                       ,y36
                       ,y37
                       ,y38
                       ,y39
                       ,y40
                       ,y41
                       ,y42
                       ,y43
                       ,y44
                       ,y45
                       ,y46
                       ,y47
                       ,y48
                       ,y49
                       ,y50
                       ,y51
                       ,y52
                       ,y53
                       ,y54
                       ,y55
                       ,y56
                       ,y57
                       ,y58
                       ,y59
                       ,(y60
                        ,y61
                        ,y62
                        ,y63
                        ,y64
                        ,y65
                        ,y66
                        ,y67
                        ,y68
                        ,y69
                        ,y70
                        ,y71
                        ,y72
                        ,y73
                        ,y74
                        ,y75
                        ,y76
                        ,y77
                        ,y78
                        ,y79
                        ,y80
                        ,y81
                        ,y82
                        ,y83
                        ,y84
                        ,y85
                        ,y86
                        ,y87
                        ,y88
                        ,y89
                        ,y90
                        ,y91
                        ,y92
                        ,y93
                        ,y94
                        ,y95
                        ,y96
                        ,y97
                        ,y98
                        ,y99
                        ,y100
                        ,y101
                        ,y102
                        ,y103
                        ,y104
                        ,y105
                        ,y106
                        ,y107
                        ,y108
                        ,y109
                        ,y110
                        ,y111
                        ,y112
                        ,y113
                        ,y114
                        ,y115
                        ,y116
                        ,y117
                        ,y118
                        ,y119
                        ,y120
                        ,(y121
                         ,y122
                         ,y123
                         ,y124
                         ,y125
                         ,y126
                         ,y127
                         ,y128
                         ,y129
                         ,y130
                         ,y131
                         ,y132
                         ,y133
                         ,y134
                         ,y135
                         ,y136
                         ,y137
                         ,y138
                         ,y139
                         ,y140
                         ,y141
                         ,y142
                         ,y143
                         ,y144
                         ,y145
                         ,y146
                         ,y147
                         ,y148
                         ,y149
                         ,y150
                         ,y151
                         ,y152
                         ,y153
                         ,y154
                         ,y155
                         ,y156
                         ,y157
                         ,y158
                         ,y159
                         ,y160
                         ,y161
                         ,y162
                         ,y163
                         ,y164
                         ,y165
                         ,y166
                         ,y167
                         ,y168
                         ,y169
                         ,y170
                         ,y171
                         ,y172
                         ,y173
                         ,y174
                         ,y175
                         ,y176
                         ,y177
                         ,y178
                         ,y179
                         ,y180
                         ,y181
                         ,(y182
                          ,y183
                          ,y184
                          ,y185
                          ,y186
                          ,y187
                          ,y188
                          ,y189
                          ,y190
                          ,y191
                          ,y192
                          ,y193
                          ,y194
                          ,y195
                          ,y196
                          ,y197
                          ,y198)))) -> mconcat [(case y of
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
                                                   Right z6 -> word8 (fromIntegral 1))
                                               ,(case y7 of
                                                   Left z7 -> word8 (fromIntegral 0)
                                                   Right z7 -> word8 (fromIntegral 1))
                                               ,(case y8 of
                                                   Left z8 -> word8 (fromIntegral 0)
                                                   Right z8 -> word8 (fromIntegral 1))
                                               ,(case y9 of
                                                   Left z9 -> word8 (fromIntegral 0)
                                                   Right z9 -> word8 (fromIntegral 1))
                                               ,(case y10 of
                                                   Left z10 -> word8 (fromIntegral 0)
                                                   Right z10 -> word8 (fromIntegral 1))
                                               ,(case y11 of
                                                   Left z11 -> word8 (fromIntegral 0)
                                                   Right z11 -> word8 (fromIntegral 1))
                                               ,(case y12 of
                                                   Left z12 -> word8 (fromIntegral 0)
                                                   Right z12 -> word8 (fromIntegral 1))
                                               ,(case y13 of
                                                   Left z13 -> word8 (fromIntegral 0)
                                                   Right z13 -> word8 (fromIntegral 1))
                                               ,(case y14 of
                                                   Left z14 -> word8 (fromIntegral 0)
                                                   Right z14 -> word8 (fromIntegral 1))
                                               ,(case y15 of
                                                   Left z15 -> word8 (fromIntegral 0)
                                                   Right z15 -> word8 (fromIntegral 1))
                                               ,(case y16 of
                                                   Left z16 -> word8 (fromIntegral 0)
                                                   Right z16 -> word8 (fromIntegral 1))
                                               ,(case y17 of
                                                   Left z17 -> word8 (fromIntegral 0)
                                                   Right z17 -> word8 (fromIntegral 1))
                                               ,(case y18 of
                                                   Left z18 -> word8 (fromIntegral 0)
                                                   Right z18 -> word8 (fromIntegral 1))
                                               ,(case y19 of
                                                   Left z19 -> word8 (fromIntegral 0)
                                                   Right z19 -> word8 (fromIntegral 1))
                                               ,(case y20 of
                                                   Left z20 -> word8 (fromIntegral 0)
                                                   Right z20 -> word8 (fromIntegral 1))
                                               ,(case y21 of
                                                   Left z21 -> word8 (fromIntegral 0)
                                                   Right z21 -> word8 (fromIntegral 1))
                                               ,(case y22 of
                                                   Left z22 -> word8 (fromIntegral 0)
                                                   Right z22 -> word8 (fromIntegral 1))
                                               ,(case y23 of
                                                   Left z23 -> word8 (fromIntegral 0)
                                                   Right z23 -> word8 (fromIntegral 1))
                                               ,(case y24 of
                                                   Left z24 -> word8 (fromIntegral 0)
                                                   Right z24 -> word8 (fromIntegral 1))
                                               ,(case y25 of
                                                   Left z25 -> word8 (fromIntegral 0)
                                                   Right z25 -> word8 (fromIntegral 1))
                                               ,(case y26 of
                                                   Left z26 -> word8 (fromIntegral 0)
                                                   Right z26 -> word8 (fromIntegral 1))
                                               ,(case y27 of
                                                   Left z27 -> word8 (fromIntegral 0)
                                                   Right z27 -> word8 (fromIntegral 1))
                                               ,(case y28 of
                                                   Left z28 -> word8 (fromIntegral 0)
                                                   Right z28 -> word8 (fromIntegral 1))
                                               ,(case y29 of
                                                   Left z29 -> word8 (fromIntegral 0)
                                                   Right z29 -> word8 (fromIntegral 1))
                                               ,(case y30 of
                                                   Left z30 -> word8 (fromIntegral 0)
                                                   Right z30 -> word8 (fromIntegral 1))
                                               ,(case y31 of
                                                   Left z31 -> word8 (fromIntegral 0)
                                                   Right z31 -> word8 (fromIntegral 1))
                                               ,(case y32 of
                                                   Left z32 -> word8 (fromIntegral 0)
                                                   Right z32 -> word8 (fromIntegral 1))
                                               ,(case y33 of
                                                   Left z33 -> word8 (fromIntegral 0)
                                                   Right z33 -> word8 (fromIntegral 1))
                                               ,(case y34 of
                                                   Left z34 -> word8 (fromIntegral 0)
                                                   Right z34 -> word8 (fromIntegral 1))
                                               ,(case y35 of
                                                   Left z35 -> word8 (fromIntegral 0)
                                                   Right z35 -> word8 (fromIntegral 1))
                                               ,(case y36 of
                                                   Left z36 -> word8 (fromIntegral 0)
                                                   Right z36 -> word8 (fromIntegral 1))
                                               ,(case y37 of
                                                   Left z37 -> word8 (fromIntegral 0)
                                                   Right z37 -> word8 (fromIntegral 1))
                                               ,(case y38 of
                                                   Left z38 -> word8 (fromIntegral 0)
                                                   Right z38 -> word8 (fromIntegral 1))
                                               ,(case y39 of
                                                   Left z39 -> word8 (fromIntegral 0)
                                                   Right z39 -> word8 (fromIntegral 1))
                                               ,(case y40 of
                                                   Left z40 -> word8 (fromIntegral 0)
                                                   Right z40 -> word8 (fromIntegral 1))
                                               ,(case y41 of
                                                   Left z41 -> word8 (fromIntegral 0)
                                                   Right z41 -> word8 (fromIntegral 1))
                                               ,(case y42 of
                                                   Left z42 -> word8 (fromIntegral 0)
                                                   Right z42 -> word8 (fromIntegral 1))
                                               ,(case y43 of
                                                   Left z43 -> word8 (fromIntegral 0)
                                                   Right z43 -> word8 (fromIntegral 1))
                                               ,(case y44 of
                                                   Left z44 -> word8 (fromIntegral 0)
                                                   Right z44 -> word8 (fromIntegral 1))
                                               ,(case y45 of
                                                   Left z45 -> word8 (fromIntegral 0)
                                                   Right z45 -> word8 (fromIntegral 1))
                                               ,(case y46 of
                                                   Left z46 -> word8 (fromIntegral 0)
                                                   Right z46 -> word8 (fromIntegral 1))
                                               ,(case y47 of
                                                   Left z47 -> word8 (fromIntegral 0)
                                                   Right z47 -> word8 (fromIntegral 1))
                                               ,(case y48 of
                                                   Left z48 -> word8 (fromIntegral 0)
                                                   Right z48 -> word8 (fromIntegral 1))
                                               ,(case y49 of
                                                   Left z49 -> word8 (fromIntegral 0)
                                                   Right z49 -> word8 (fromIntegral 1))
                                               ,(case y50 of
                                                   Left z50 -> word8 (fromIntegral 0)
                                                   Right z50 -> word8 (fromIntegral 1))
                                               ,(case y51 of
                                                   Left z51 -> word8 (fromIntegral 0)
                                                   Right z51 -> word8 (fromIntegral 1))
                                               ,(case y52 of
                                                   Left z52 -> word8 (fromIntegral 0)
                                                   Right z52 -> word8 (fromIntegral 1))
                                               ,(case y53 of
                                                   Left z53 -> word8 (fromIntegral 0)
                                                   Right z53 -> word8 (fromIntegral 1))
                                               ,(case y54 of
                                                   Left z54 -> word8 (fromIntegral 0)
                                                   Right z54 -> word8 (fromIntegral 1))
                                               ,(case y55 of
                                                   Left z55 -> word8 (fromIntegral 0)
                                                   Right z55 -> word8 (fromIntegral 1))
                                               ,(case y56 of
                                                   Left z56 -> word8 (fromIntegral 0)
                                                   Right z56 -> word8 (fromIntegral 1))
                                               ,(case y57 of
                                                   Left z57 -> word8 (fromIntegral 0)
                                                   Right z57 -> word8 (fromIntegral 1))
                                               ,(case y58 of
                                                   Left z58 -> word8 (fromIntegral 0)
                                                   Right z58 -> word8 (fromIntegral 1))
                                               ,(case y59 of
                                                   Left z59 -> word8 (fromIntegral 0)
                                                   Right z59 -> word8 (fromIntegral 1))
                                               ,(case y60 of
                                                   Left z60 -> word8 (fromIntegral 0)
                                                   Right z60 -> word8 (fromIntegral 1))
                                               ,(case y61 of
                                                   Left z61 -> word8 (fromIntegral 0)
                                                   Right z61 -> word8 (fromIntegral 1))
                                               ,(case y62 of
                                                   Left z62 -> word8 (fromIntegral 0)
                                                   Right z62 -> word8 (fromIntegral 1))
                                               ,(case y63 of
                                                   Left z63 -> word8 (fromIntegral 0)
                                                   Right z63 -> word8 (fromIntegral 1))
                                               ,(case y64 of
                                                   Left z64 -> word8 (fromIntegral 0)
                                                   Right z64 -> word8 (fromIntegral 1))
                                               ,(case y65 of
                                                   Left z65 -> word8 (fromIntegral 0)
                                                   Right z65 -> word8 (fromIntegral 1))
                                               ,(case y66 of
                                                   Left z66 -> word8 (fromIntegral 0)
                                                   Right z66 -> word8 (fromIntegral 1))
                                               ,(case y67 of
                                                   Left z67 -> word8 (fromIntegral 0)
                                                   Right z67 -> word8 (fromIntegral 1))
                                               ,(case y68 of
                                                   Left z68 -> word8 (fromIntegral 0)
                                                   Right z68 -> word8 (fromIntegral 1))
                                               ,(case y69 of
                                                   Left z69 -> word8 (fromIntegral 0)
                                                   Right z69 -> word8 (fromIntegral 1))
                                               ,(case y70 of
                                                   Left z70 -> word8 (fromIntegral 0)
                                                   Right z70 -> word8 (fromIntegral 1))
                                               ,(case y71 of
                                                   Left z71 -> word8 (fromIntegral 0)
                                                   Right z71 -> word8 (fromIntegral 1))
                                               ,(case y72 of
                                                   Left z72 -> word8 (fromIntegral 0)
                                                   Right z72 -> word8 (fromIntegral 1))
                                               ,(case y73 of
                                                   Left z73 -> word8 (fromIntegral 0)
                                                   Right z73 -> word8 (fromIntegral 1))
                                               ,(case y74 of
                                                   Left z74 -> word8 (fromIntegral 0)
                                                   Right z74 -> word8 (fromIntegral 1))
                                               ,(case y75 of
                                                   Left z75 -> word8 (fromIntegral 0)
                                                   Right z75 -> word8 (fromIntegral 1))
                                               ,(case y76 of
                                                   Left z76 -> word8 (fromIntegral 0)
                                                   Right z76 -> word8 (fromIntegral 1))
                                               ,(case y77 of
                                                   Left z77 -> word8 (fromIntegral 0)
                                                   Right z77 -> word8 (fromIntegral 1))
                                               ,(case y78 of
                                                   Left z78 -> word8 (fromIntegral 0)
                                                   Right z78 -> word8 (fromIntegral 1))
                                               ,(case y79 of
                                                   Left z79 -> word8 (fromIntegral 0)
                                                   Right z79 -> word8 (fromIntegral 1))
                                               ,(case y80 of
                                                   Left z80 -> word8 (fromIntegral 0)
                                                   Right z80 -> word8 (fromIntegral 1))
                                               ,(case y81 of
                                                   Left z81 -> word8 (fromIntegral 0)
                                                   Right z81 -> word8 (fromIntegral 1))
                                               ,(case y82 of
                                                   Left z82 -> word8 (fromIntegral 0)
                                                   Right z82 -> word8 (fromIntegral 1))
                                               ,(case y83 of
                                                   Left z83 -> word8 (fromIntegral 0)
                                                   Right z83 -> word8 (fromIntegral 1))
                                               ,(case y84 of
                                                   Left z84 -> word8 (fromIntegral 0)
                                                   Right z84 -> word8 (fromIntegral 1))
                                               ,(case y85 of
                                                   Left z85 -> word8 (fromIntegral 0)
                                                   Right z85 -> word8 (fromIntegral 1))
                                               ,(case y86 of
                                                   Left z86 -> word8 (fromIntegral 0)
                                                   Right z86 -> word8 (fromIntegral 1))
                                               ,(case y87 of
                                                   Left z87 -> word8 (fromIntegral 0)
                                                   Right z87 -> word8 (fromIntegral 1))
                                               ,(case y88 of
                                                   Left z88 -> word8 (fromIntegral 0)
                                                   Right z88 -> word8 (fromIntegral 1))
                                               ,(case y89 of
                                                   Left z89 -> word8 (fromIntegral 0)
                                                   Right z89 -> word8 (fromIntegral 1))
                                               ,(case y90 of
                                                   Left z90 -> word8 (fromIntegral 0)
                                                   Right z90 -> word8 (fromIntegral 1))
                                               ,(case y91 of
                                                   Left z91 -> word8 (fromIntegral 0)
                                                   Right z91 -> word8 (fromIntegral 1))
                                               ,(case y92 of
                                                   Left z92 -> word8 (fromIntegral 0)
                                                   Right z92 -> word8 (fromIntegral 1))
                                               ,(case y93 of
                                                   Left z93 -> word8 (fromIntegral 0)
                                                   Right z93 -> word8 (fromIntegral 1))
                                               ,(case y94 of
                                                   Left z94 -> word8 (fromIntegral 0)
                                                   Right z94 -> word8 (fromIntegral 1))
                                               ,(case y95 of
                                                   Left z95 -> word8 (fromIntegral 0)
                                                   Right z95 -> word8 (fromIntegral 1))
                                               ,(case y96 of
                                                   Left z96 -> word8 (fromIntegral 0)
                                                   Right z96 -> word8 (fromIntegral 1))
                                               ,(case y97 of
                                                   Left z97 -> word8 (fromIntegral 0)
                                                   Right z97 -> word8 (fromIntegral 1))
                                               ,(case y98 of
                                                   Left z98 -> word8 (fromIntegral 0)
                                                   Right z98 -> word8 (fromIntegral 1))
                                               ,(case y99 of
                                                   Left z99 -> word8 (fromIntegral 0)
                                                   Right z99 -> word8 (fromIntegral 1))
                                               ,(case y100 of
                                                   Left z100 -> word8 (fromIntegral 0)
                                                   Right z100 -> word8 (fromIntegral 1))
                                               ,(case y101 of
                                                   Left z101 -> word8 (fromIntegral 0)
                                                   Right z101 -> word8 (fromIntegral 1))
                                               ,(case y102 of
                                                   Left z102 -> word8 (fromIntegral 0)
                                                   Right z102 -> word8 (fromIntegral 1))
                                               ,(case y103 of
                                                   Left z103 -> word8 (fromIntegral 0)
                                                   Right z103 -> word8 (fromIntegral 1))
                                               ,(case y104 of
                                                   Left z104 -> word8 (fromIntegral 0)
                                                   Right z104 -> word8 (fromIntegral 1))
                                               ,(case y105 of
                                                   Left z105 -> word8 (fromIntegral 0)
                                                   Right z105 -> word8 (fromIntegral 1))
                                               ,(case y106 of
                                                   Left z106 -> word8 (fromIntegral 0)
                                                   Right z106 -> word8 (fromIntegral 1))
                                               ,(case y107 of
                                                   Left z107 -> word8 (fromIntegral 0)
                                                   Right z107 -> word8 (fromIntegral 1))
                                               ,(case y108 of
                                                   Left z108 -> word8 (fromIntegral 0)
                                                   Right z108 -> word8 (fromIntegral 1))
                                               ,(case y109 of
                                                   Left z109 -> word8 (fromIntegral 0)
                                                   Right z109 -> word8 (fromIntegral 1))
                                               ,(case y110 of
                                                   Left z110 -> word8 (fromIntegral 0)
                                                   Right z110 -> word8 (fromIntegral 1))
                                               ,(case y111 of
                                                   Left z111 -> word8 (fromIntegral 0)
                                                   Right z111 -> word8 (fromIntegral 1))
                                               ,(case y112 of
                                                   Left z112 -> word8 (fromIntegral 0)
                                                   Right z112 -> word8 (fromIntegral 1))
                                               ,(case y113 of
                                                   Left z113 -> word8 (fromIntegral 0)
                                                   Right z113 -> word8 (fromIntegral 1))
                                               ,(case y114 of
                                                   Left z114 -> word8 (fromIntegral 0)
                                                   Right z114 -> word8 (fromIntegral 1))
                                               ,(case y115 of
                                                   Left z115 -> word8 (fromIntegral 0)
                                                   Right z115 -> word8 (fromIntegral 1))
                                               ,(case y116 of
                                                   Left z116 -> word8 (fromIntegral 0)
                                                   Right z116 -> word8 (fromIntegral 1))
                                               ,(case y117 of
                                                   Left z117 -> word8 (fromIntegral 0)
                                                   Right z117 -> word8 (fromIntegral 1))
                                               ,(case y118 of
                                                   Left z118 -> word8 (fromIntegral 0)
                                                   Right z118 -> word8 (fromIntegral 1))
                                               ,(case y119 of
                                                   Left z119 -> word8 (fromIntegral 0)
                                                   Right z119 -> word8 (fromIntegral 1))
                                               ,(case y120 of
                                                   Left z120 -> word8 (fromIntegral 0)
                                                   Right z120 -> word8 (fromIntegral 1))
                                               ,(case y121 of
                                                   Left z121 -> word8 (fromIntegral 0)
                                                   Right z121 -> word8 (fromIntegral 1))
                                               ,(case y122 of
                                                   Left z122 -> word8 (fromIntegral 0)
                                                   Right z122 -> word8 (fromIntegral 1))
                                               ,(case y123 of
                                                   Left z123 -> word8 (fromIntegral 0)
                                                   Right z123 -> word8 (fromIntegral 1))
                                               ,(case y124 of
                                                   Left z124 -> word8 (fromIntegral 0)
                                                   Right z124 -> word8 (fromIntegral 1))
                                               ,(case y125 of
                                                   Left z125 -> word8 (fromIntegral 0)
                                                   Right z125 -> word8 (fromIntegral 1))
                                               ,(case y126 of
                                                   Left z126 -> word8 (fromIntegral 0)
                                                   Right z126 -> word8 (fromIntegral 1))
                                               ,(case y127 of
                                                   Left z127 -> word8 (fromIntegral 0)
                                                   Right z127 -> word8 (fromIntegral 1))
                                               ,(case y128 of
                                                   Left z128 -> word8 (fromIntegral 0)
                                                   Right z128 -> word8 (fromIntegral 1))
                                               ,(case y129 of
                                                   Left z129 -> word8 (fromIntegral 0)
                                                   Right z129 -> word8 (fromIntegral 1))
                                               ,(case y130 of
                                                   Left z130 -> word8 (fromIntegral 0)
                                                   Right z130 -> word8 (fromIntegral 1))
                                               ,(case y131 of
                                                   Left z131 -> word8 (fromIntegral 0)
                                                   Right z131 -> word8 (fromIntegral 1))
                                               ,(case y132 of
                                                   Left z132 -> word8 (fromIntegral 0)
                                                   Right z132 -> word8 (fromIntegral 1))
                                               ,(case y133 of
                                                   Left z133 -> word8 (fromIntegral 0)
                                                   Right z133 -> word8 (fromIntegral 1))
                                               ,(case y134 of
                                                   Left z134 -> word8 (fromIntegral 0)
                                                   Right z134 -> word8 (fromIntegral 1))
                                               ,(case y135 of
                                                   Left z135 -> word8 (fromIntegral 0)
                                                   Right z135 -> word8 (fromIntegral 1))
                                               ,(case y136 of
                                                   Left z136 -> word8 (fromIntegral 0)
                                                   Right z136 -> word8 (fromIntegral 1))
                                               ,(case y137 of
                                                   Left z137 -> word8 (fromIntegral 0)
                                                   Right z137 -> word8 (fromIntegral 1))
                                               ,(case y138 of
                                                   Left z138 -> word8 (fromIntegral 0)
                                                   Right z138 -> word8 (fromIntegral 1))
                                               ,(case y139 of
                                                   Left z139 -> word8 (fromIntegral 0)
                                                   Right z139 -> word8 (fromIntegral 1))
                                               ,(case y140 of
                                                   Left z140 -> word8 (fromIntegral 0)
                                                   Right z140 -> word8 (fromIntegral 1))
                                               ,(case y141 of
                                                   Left z141 -> word8 (fromIntegral 0)
                                                   Right z141 -> word8 (fromIntegral 1))
                                               ,(case y142 of
                                                   Left z142 -> word8 (fromIntegral 0)
                                                   Right z142 -> word8 (fromIntegral 1))
                                               ,(case y143 of
                                                   Left z143 -> word8 (fromIntegral 0)
                                                   Right z143 -> word8 (fromIntegral 1))
                                               ,(case y144 of
                                                   Left z144 -> word8 (fromIntegral 0)
                                                   Right z144 -> word8 (fromIntegral 1))
                                               ,(case y145 of
                                                   Left z145 -> word8 (fromIntegral 0)
                                                   Right z145 -> word8 (fromIntegral 1))
                                               ,(case y146 of
                                                   Left z146 -> word8 (fromIntegral 0)
                                                   Right z146 -> word8 (fromIntegral 1))
                                               ,(case y147 of
                                                   Left z147 -> word8 (fromIntegral 0)
                                                   Right z147 -> word8 (fromIntegral 1))
                                               ,(case y148 of
                                                   Left z148 -> word8 (fromIntegral 0)
                                                   Right z148 -> word8 (fromIntegral 1))
                                               ,(case y149 of
                                                   Left z149 -> word8 (fromIntegral 0)
                                                   Right z149 -> word8 (fromIntegral 1))
                                               ,(case y150 of
                                                   Left z150 -> word8 (fromIntegral 0)
                                                   Right z150 -> word8 (fromIntegral 1))
                                               ,(case y151 of
                                                   Left z151 -> word8 (fromIntegral 0)
                                                   Right z151 -> word8 (fromIntegral 1))
                                               ,(case y152 of
                                                   Left z152 -> word8 (fromIntegral 0)
                                                   Right z152 -> word8 (fromIntegral 1))
                                               ,(case y153 of
                                                   Left z153 -> word8 (fromIntegral 0)
                                                   Right z153 -> word8 (fromIntegral 1))
                                               ,(case y154 of
                                                   Left z154 -> word8 (fromIntegral 0)
                                                   Right z154 -> word8 (fromIntegral 1))
                                               ,(case y155 of
                                                   Left z155 -> word8 (fromIntegral 0)
                                                   Right z155 -> word8 (fromIntegral 1))
                                               ,(case y156 of
                                                   Left z156 -> word8 (fromIntegral 0)
                                                   Right z156 -> word8 (fromIntegral 1))
                                               ,(case y157 of
                                                   Left z157 -> word8 (fromIntegral 0)
                                                   Right z157 -> word8 (fromIntegral 1))
                                               ,(case y158 of
                                                   Left z158 -> word8 (fromIntegral 0)
                                                   Right z158 -> word8 (fromIntegral 1))
                                               ,(case y159 of
                                                   Left z159 -> word8 (fromIntegral 0)
                                                   Right z159 -> word8 (fromIntegral 1))
                                               ,(case y160 of
                                                   Left z160 -> word8 (fromIntegral 0)
                                                   Right z160 -> word8 (fromIntegral 1))
                                               ,(case y161 of
                                                   Left z161 -> word8 (fromIntegral 0)
                                                   Right z161 -> word8 (fromIntegral 1))
                                               ,(case y162 of
                                                   Left z162 -> word8 (fromIntegral 0)
                                                   Right z162 -> word8 (fromIntegral 1))
                                               ,(case y163 of
                                                   Left z163 -> word8 (fromIntegral 0)
                                                   Right z163 -> word8 (fromIntegral 1))
                                               ,(case y164 of
                                                   Left z164 -> word8 (fromIntegral 0)
                                                   Right z164 -> word8 (fromIntegral 1))
                                               ,(case y165 of
                                                   Left z165 -> word8 (fromIntegral 0)
                                                   Right z165 -> word8 (fromIntegral 1))
                                               ,(case y166 of
                                                   Left z166 -> word8 (fromIntegral 0)
                                                   Right z166 -> word8 (fromIntegral 1))
                                               ,(case y167 of
                                                   Left z167 -> word8 (fromIntegral 0)
                                                   Right z167 -> word8 (fromIntegral 1))
                                               ,(case y168 of
                                                   Left z168 -> word8 (fromIntegral 0)
                                                   Right z168 -> word8 (fromIntegral 1))
                                               ,(case y169 of
                                                   Left z169 -> word8 (fromIntegral 0)
                                                   Right z169 -> word8 (fromIntegral 1))
                                               ,(case y170 of
                                                   Left z170 -> word8 (fromIntegral 0)
                                                   Right z170 -> word8 (fromIntegral 1))
                                               ,(case y171 of
                                                   Left z171 -> word8 (fromIntegral 0)
                                                   Right z171 -> word8 (fromIntegral 1))
                                               ,(case y172 of
                                                   Left z172 -> word8 (fromIntegral 0)
                                                   Right z172 -> word8 (fromIntegral 1))
                                               ,(case y173 of
                                                   Left z173 -> word8 (fromIntegral 0)
                                                   Right z173 -> word8 (fromIntegral 1))
                                               ,(case y174 of
                                                   Left z174 -> word8 (fromIntegral 0)
                                                   Right z174 -> word8 (fromIntegral 1))
                                               ,(case y175 of
                                                   Left z175 -> word8 (fromIntegral 0)
                                                   Right z175 -> word8 (fromIntegral 1))
                                               ,(case y176 of
                                                   Left z176 -> word8 (fromIntegral 0)
                                                   Right z176 -> word8 (fromIntegral 1))
                                               ,(case y177 of
                                                   Left z177 -> word8 (fromIntegral 0)
                                                   Right z177 -> word8 (fromIntegral 1))
                                               ,(case y178 of
                                                   Left z178 -> word8 (fromIntegral 0)
                                                   Right z178 -> word8 (fromIntegral 1))
                                               ,(case y179 of
                                                   Left z179 -> word8 (fromIntegral 0)
                                                   Right z179 -> word8 (fromIntegral 1))
                                               ,(case y180 of
                                                   Left z180 -> word8 (fromIntegral 0)
                                                   Right z180 -> word8 (fromIntegral 1))
                                               ,(case y181 of
                                                   Left z181 -> word8 (fromIntegral 0)
                                                   Right z181 -> word8 (fromIntegral 1))
                                               ,(case y182 of
                                                   Left z182 -> word8 (fromIntegral 0)
                                                   Right z182 -> word8 (fromIntegral 1))
                                               ,(case y183 of
                                                   Left z183 -> word8 (fromIntegral 0)
                                                   Right z183 -> word8 (fromIntegral 1))
                                               ,(case y184 of
                                                   Left z184 -> word8 (fromIntegral 0)
                                                   Right z184 -> word8 (fromIntegral 1))
                                               ,(case y185 of
                                                   Left z185 -> word8 (fromIntegral 0)
                                                   Right z185 -> word8 (fromIntegral 1))
                                               ,(case y186 of
                                                   Left z186 -> word8 (fromIntegral 0)
                                                   Right z186 -> word8 (fromIntegral 1))
                                               ,(case y187 of
                                                   Left z187 -> word8 (fromIntegral 0)
                                                   Right z187 -> word8 (fromIntegral 1))
                                               ,(case y188 of
                                                   Left z188 -> word8 (fromIntegral 0)
                                                   Right z188 -> word8 (fromIntegral 1))
                                               ,(case y189 of
                                                   Left z189 -> word8 (fromIntegral 0)
                                                   Right z189 -> word8 (fromIntegral 1))
                                               ,(case y190 of
                                                   Left z190 -> word8 (fromIntegral 0)
                                                   Right z190 -> word8 (fromIntegral 1))
                                               ,(case y191 of
                                                   Left z191 -> word8 (fromIntegral 0)
                                                   Right z191 -> word8 (fromIntegral 1))
                                               ,(case y192 of
                                                   Left z192 -> word8 (fromIntegral 0)
                                                   Right z192 -> word8 (fromIntegral 1))
                                               ,(case y193 of
                                                   Left z193 -> word8 (fromIntegral 0)
                                                   Right z193 -> word8 (fromIntegral 1))
                                               ,(case y194 of
                                                   Left z194 -> word8 (fromIntegral 0)
                                                   Right z194 -> word8 (fromIntegral 1))
                                               ,(case y195 of
                                                   Left z195 -> word8 (fromIntegral 0)
                                                   Right z195 -> word8 (fromIntegral 1))
                                               ,(case y196 of
                                                   Left z196 -> word8 (fromIntegral 0)
                                                   Right z196 -> word8 (fromIntegral 1))
                                               ,(case y197 of
                                                   Left z197 -> word8 (fromIntegral 0)
                                                   Right z197 -> word8 (fromIntegral 1))
                                               ,(case y198 of
                                                   Left z198 -> word8 (fromIntegral 0)
                                                   Right z198 -> word8 (fromIntegral 1))]

decodeLargeTuple :: Deserialiser LargeTuple
decodeLargeTuple = do
                     x <- do
                            i <- deserialiseInt
                            case i of
                              0 -> return (Left ())
                              1 -> return (Right ())
                              _ -> failDecode
                     x0 <- do
                             i0 <- deserialiseInt
                             case i0 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x1 <- do
                             i1 <- deserialiseInt
                             case i1 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x2 <- do
                             i2 <- deserialiseInt
                             case i2 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x3 <- do
                             i3 <- deserialiseInt
                             case i3 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x4 <- do
                             i4 <- deserialiseInt
                             case i4 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x5 <- do
                             i5 <- deserialiseInt
                             case i5 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x6 <- do
                             i6 <- deserialiseInt
                             case i6 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x7 <- do
                             i7 <- deserialiseInt
                             case i7 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x8 <- do
                             i8 <- deserialiseInt
                             case i8 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x9 <- do
                             i9 <- deserialiseInt
                             case i9 of
                               0 -> return (Left ())
                               1 -> return (Right ())
                               _ -> failDecode
                     x10 <- do
                              i10 <- deserialiseInt
                              case i10 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x11 <- do
                              i11 <- deserialiseInt
                              case i11 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x12 <- do
                              i12 <- deserialiseInt
                              case i12 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x13 <- do
                              i13 <- deserialiseInt
                              case i13 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x14 <- do
                              i14 <- deserialiseInt
                              case i14 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x15 <- do
                              i15 <- deserialiseInt
                              case i15 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x16 <- do
                              i16 <- deserialiseInt
                              case i16 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x17 <- do
                              i17 <- deserialiseInt
                              case i17 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x18 <- do
                              i18 <- deserialiseInt
                              case i18 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x19 <- do
                              i19 <- deserialiseInt
                              case i19 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x20 <- do
                              i20 <- deserialiseInt
                              case i20 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x21 <- do
                              i21 <- deserialiseInt
                              case i21 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x22 <- do
                              i22 <- deserialiseInt
                              case i22 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x23 <- do
                              i23 <- deserialiseInt
                              case i23 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x24 <- do
                              i24 <- deserialiseInt
                              case i24 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x25 <- do
                              i25 <- deserialiseInt
                              case i25 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x26 <- do
                              i26 <- deserialiseInt
                              case i26 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x27 <- do
                              i27 <- deserialiseInt
                              case i27 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x28 <- do
                              i28 <- deserialiseInt
                              case i28 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x29 <- do
                              i29 <- deserialiseInt
                              case i29 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x30 <- do
                              i30 <- deserialiseInt
                              case i30 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x31 <- do
                              i31 <- deserialiseInt
                              case i31 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x32 <- do
                              i32 <- deserialiseInt
                              case i32 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x33 <- do
                              i33 <- deserialiseInt
                              case i33 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x34 <- do
                              i34 <- deserialiseInt
                              case i34 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x35 <- do
                              i35 <- deserialiseInt
                              case i35 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x36 <- do
                              i36 <- deserialiseInt
                              case i36 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x37 <- do
                              i37 <- deserialiseInt
                              case i37 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x38 <- do
                              i38 <- deserialiseInt
                              case i38 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x39 <- do
                              i39 <- deserialiseInt
                              case i39 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x40 <- do
                              i40 <- deserialiseInt
                              case i40 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x41 <- do
                              i41 <- deserialiseInt
                              case i41 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x42 <- do
                              i42 <- deserialiseInt
                              case i42 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x43 <- do
                              i43 <- deserialiseInt
                              case i43 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x44 <- do
                              i44 <- deserialiseInt
                              case i44 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x45 <- do
                              i45 <- deserialiseInt
                              case i45 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x46 <- do
                              i46 <- deserialiseInt
                              case i46 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x47 <- do
                              i47 <- deserialiseInt
                              case i47 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x48 <- do
                              i48 <- deserialiseInt
                              case i48 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x49 <- do
                              i49 <- deserialiseInt
                              case i49 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x50 <- do
                              i50 <- deserialiseInt
                              case i50 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x51 <- do
                              i51 <- deserialiseInt
                              case i51 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x52 <- do
                              i52 <- deserialiseInt
                              case i52 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x53 <- do
                              i53 <- deserialiseInt
                              case i53 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x54 <- do
                              i54 <- deserialiseInt
                              case i54 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x55 <- do
                              i55 <- deserialiseInt
                              case i55 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x56 <- do
                              i56 <- deserialiseInt
                              case i56 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x57 <- do
                              i57 <- deserialiseInt
                              case i57 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x58 <- do
                              i58 <- deserialiseInt
                              case i58 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x59 <- do
                              i59 <- deserialiseInt
                              case i59 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x60 <- do
                              i60 <- deserialiseInt
                              case i60 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x61 <- do
                              i61 <- deserialiseInt
                              case i61 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x62 <- do
                              i62 <- deserialiseInt
                              case i62 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x63 <- do
                              i63 <- deserialiseInt
                              case i63 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x64 <- do
                              i64 <- deserialiseInt
                              case i64 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x65 <- do
                              i65 <- deserialiseInt
                              case i65 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x66 <- do
                              i66 <- deserialiseInt
                              case i66 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x67 <- do
                              i67 <- deserialiseInt
                              case i67 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x68 <- do
                              i68 <- deserialiseInt
                              case i68 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x69 <- do
                              i69 <- deserialiseInt
                              case i69 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x70 <- do
                              i70 <- deserialiseInt
                              case i70 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x71 <- do
                              i71 <- deserialiseInt
                              case i71 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x72 <- do
                              i72 <- deserialiseInt
                              case i72 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x73 <- do
                              i73 <- deserialiseInt
                              case i73 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x74 <- do
                              i74 <- deserialiseInt
                              case i74 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x75 <- do
                              i75 <- deserialiseInt
                              case i75 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x76 <- do
                              i76 <- deserialiseInt
                              case i76 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x77 <- do
                              i77 <- deserialiseInt
                              case i77 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x78 <- do
                              i78 <- deserialiseInt
                              case i78 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x79 <- do
                              i79 <- deserialiseInt
                              case i79 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x80 <- do
                              i80 <- deserialiseInt
                              case i80 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x81 <- do
                              i81 <- deserialiseInt
                              case i81 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x82 <- do
                              i82 <- deserialiseInt
                              case i82 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x83 <- do
                              i83 <- deserialiseInt
                              case i83 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x84 <- do
                              i84 <- deserialiseInt
                              case i84 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x85 <- do
                              i85 <- deserialiseInt
                              case i85 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x86 <- do
                              i86 <- deserialiseInt
                              case i86 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x87 <- do
                              i87 <- deserialiseInt
                              case i87 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x88 <- do
                              i88 <- deserialiseInt
                              case i88 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x89 <- do
                              i89 <- deserialiseInt
                              case i89 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x90 <- do
                              i90 <- deserialiseInt
                              case i90 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x91 <- do
                              i91 <- deserialiseInt
                              case i91 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x92 <- do
                              i92 <- deserialiseInt
                              case i92 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x93 <- do
                              i93 <- deserialiseInt
                              case i93 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x94 <- do
                              i94 <- deserialiseInt
                              case i94 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x95 <- do
                              i95 <- deserialiseInt
                              case i95 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x96 <- do
                              i96 <- deserialiseInt
                              case i96 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x97 <- do
                              i97 <- deserialiseInt
                              case i97 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x98 <- do
                              i98 <- deserialiseInt
                              case i98 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x99 <- do
                              i99 <- deserialiseInt
                              case i99 of
                                0 -> return (Left ())
                                1 -> return (Right ())
                                _ -> failDecode
                     x100 <- do
                               i100 <- deserialiseInt
                               case i100 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x101 <- do
                               i101 <- deserialiseInt
                               case i101 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x102 <- do
                               i102 <- deserialiseInt
                               case i102 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x103 <- do
                               i103 <- deserialiseInt
                               case i103 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x104 <- do
                               i104 <- deserialiseInt
                               case i104 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x105 <- do
                               i105 <- deserialiseInt
                               case i105 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x106 <- do
                               i106 <- deserialiseInt
                               case i106 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x107 <- do
                               i107 <- deserialiseInt
                               case i107 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x108 <- do
                               i108 <- deserialiseInt
                               case i108 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x109 <- do
                               i109 <- deserialiseInt
                               case i109 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x110 <- do
                               i110 <- deserialiseInt
                               case i110 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x111 <- do
                               i111 <- deserialiseInt
                               case i111 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x112 <- do
                               i112 <- deserialiseInt
                               case i112 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x113 <- do
                               i113 <- deserialiseInt
                               case i113 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x114 <- do
                               i114 <- deserialiseInt
                               case i114 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x115 <- do
                               i115 <- deserialiseInt
                               case i115 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x116 <- do
                               i116 <- deserialiseInt
                               case i116 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x117 <- do
                               i117 <- deserialiseInt
                               case i117 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x118 <- do
                               i118 <- deserialiseInt
                               case i118 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x119 <- do
                               i119 <- deserialiseInt
                               case i119 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x120 <- do
                               i120 <- deserialiseInt
                               case i120 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x121 <- do
                               i121 <- deserialiseInt
                               case i121 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x122 <- do
                               i122 <- deserialiseInt
                               case i122 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x123 <- do
                               i123 <- deserialiseInt
                               case i123 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x124 <- do
                               i124 <- deserialiseInt
                               case i124 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x125 <- do
                               i125 <- deserialiseInt
                               case i125 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x126 <- do
                               i126 <- deserialiseInt
                               case i126 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x127 <- do
                               i127 <- deserialiseInt
                               case i127 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x128 <- do
                               i128 <- deserialiseInt
                               case i128 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x129 <- do
                               i129 <- deserialiseInt
                               case i129 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x130 <- do
                               i130 <- deserialiseInt
                               case i130 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x131 <- do
                               i131 <- deserialiseInt
                               case i131 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x132 <- do
                               i132 <- deserialiseInt
                               case i132 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x133 <- do
                               i133 <- deserialiseInt
                               case i133 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x134 <- do
                               i134 <- deserialiseInt
                               case i134 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x135 <- do
                               i135 <- deserialiseInt
                               case i135 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x136 <- do
                               i136 <- deserialiseInt
                               case i136 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x137 <- do
                               i137 <- deserialiseInt
                               case i137 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x138 <- do
                               i138 <- deserialiseInt
                               case i138 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x139 <- do
                               i139 <- deserialiseInt
                               case i139 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x140 <- do
                               i140 <- deserialiseInt
                               case i140 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x141 <- do
                               i141 <- deserialiseInt
                               case i141 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x142 <- do
                               i142 <- deserialiseInt
                               case i142 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x143 <- do
                               i143 <- deserialiseInt
                               case i143 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x144 <- do
                               i144 <- deserialiseInt
                               case i144 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x145 <- do
                               i145 <- deserialiseInt
                               case i145 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x146 <- do
                               i146 <- deserialiseInt
                               case i146 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x147 <- do
                               i147 <- deserialiseInt
                               case i147 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x148 <- do
                               i148 <- deserialiseInt
                               case i148 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x149 <- do
                               i149 <- deserialiseInt
                               case i149 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x150 <- do
                               i150 <- deserialiseInt
                               case i150 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x151 <- do
                               i151 <- deserialiseInt
                               case i151 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x152 <- do
                               i152 <- deserialiseInt
                               case i152 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x153 <- do
                               i153 <- deserialiseInt
                               case i153 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x154 <- do
                               i154 <- deserialiseInt
                               case i154 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x155 <- do
                               i155 <- deserialiseInt
                               case i155 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x156 <- do
                               i156 <- deserialiseInt
                               case i156 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x157 <- do
                               i157 <- deserialiseInt
                               case i157 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x158 <- do
                               i158 <- deserialiseInt
                               case i158 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x159 <- do
                               i159 <- deserialiseInt
                               case i159 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x160 <- do
                               i160 <- deserialiseInt
                               case i160 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x161 <- do
                               i161 <- deserialiseInt
                               case i161 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x162 <- do
                               i162 <- deserialiseInt
                               case i162 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x163 <- do
                               i163 <- deserialiseInt
                               case i163 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x164 <- do
                               i164 <- deserialiseInt
                               case i164 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x165 <- do
                               i165 <- deserialiseInt
                               case i165 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x166 <- do
                               i166 <- deserialiseInt
                               case i166 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x167 <- do
                               i167 <- deserialiseInt
                               case i167 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x168 <- do
                               i168 <- deserialiseInt
                               case i168 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x169 <- do
                               i169 <- deserialiseInt
                               case i169 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x170 <- do
                               i170 <- deserialiseInt
                               case i170 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x171 <- do
                               i171 <- deserialiseInt
                               case i171 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x172 <- do
                               i172 <- deserialiseInt
                               case i172 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x173 <- do
                               i173 <- deserialiseInt
                               case i173 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x174 <- do
                               i174 <- deserialiseInt
                               case i174 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x175 <- do
                               i175 <- deserialiseInt
                               case i175 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x176 <- do
                               i176 <- deserialiseInt
                               case i176 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x177 <- do
                               i177 <- deserialiseInt
                               case i177 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x178 <- do
                               i178 <- deserialiseInt
                               case i178 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x179 <- do
                               i179 <- deserialiseInt
                               case i179 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x180 <- do
                               i180 <- deserialiseInt
                               case i180 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x181 <- do
                               i181 <- deserialiseInt
                               case i181 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x182 <- do
                               i182 <- deserialiseInt
                               case i182 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x183 <- do
                               i183 <- deserialiseInt
                               case i183 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x184 <- do
                               i184 <- deserialiseInt
                               case i184 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x185 <- do
                               i185 <- deserialiseInt
                               case i185 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x186 <- do
                               i186 <- deserialiseInt
                               case i186 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x187 <- do
                               i187 <- deserialiseInt
                               case i187 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x188 <- do
                               i188 <- deserialiseInt
                               case i188 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x189 <- do
                               i189 <- deserialiseInt
                               case i189 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x190 <- do
                               i190 <- deserialiseInt
                               case i190 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x191 <- do
                               i191 <- deserialiseInt
                               case i191 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x192 <- do
                               i192 <- deserialiseInt
                               case i192 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x193 <- do
                               i193 <- deserialiseInt
                               case i193 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x194 <- do
                               i194 <- deserialiseInt
                               case i194 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x195 <- do
                               i195 <- deserialiseInt
                               case i195 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x196 <- do
                               i196 <- deserialiseInt
                               case i196 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x197 <- do
                               i197 <- deserialiseInt
                               case i197 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     x198 <- do
                               i198 <- deserialiseInt
                               case i198 of
                                 0 -> return (Left ())
                                 1 -> return (Right ())
                                 _ -> failDecode
                     return (x
                            ,x0
                            ,x1
                            ,x2
                            ,x3
                            ,x4
                            ,x5
                            ,x6
                            ,x7
                            ,x8
                            ,x9
                            ,x10
                            ,x11
                            ,x12
                            ,x13
                            ,x14
                            ,x15
                            ,x16
                            ,x17
                            ,x18
                            ,x19
                            ,x20
                            ,x21
                            ,x22
                            ,x23
                            ,x24
                            ,x25
                            ,x26
                            ,x27
                            ,x28
                            ,x29
                            ,x30
                            ,x31
                            ,x32
                            ,x33
                            ,x34
                            ,x35
                            ,x36
                            ,x37
                            ,x38
                            ,x39
                            ,x40
                            ,x41
                            ,x42
                            ,x43
                            ,x44
                            ,x45
                            ,x46
                            ,x47
                            ,x48
                            ,x49
                            ,x50
                            ,x51
                            ,x52
                            ,x53
                            ,x54
                            ,x55
                            ,x56
                            ,x57
                            ,x58
                            ,x59
                            ,(x60
                             ,x61
                             ,x62
                             ,x63
                             ,x64
                             ,x65
                             ,x66
                             ,x67
                             ,x68
                             ,x69
                             ,x70
                             ,x71
                             ,x72
                             ,x73
                             ,x74
                             ,x75
                             ,x76
                             ,x77
                             ,x78
                             ,x79
                             ,x80
                             ,x81
                             ,x82
                             ,x83
                             ,x84
                             ,x85
                             ,x86
                             ,x87
                             ,x88
                             ,x89
                             ,x90
                             ,x91
                             ,x92
                             ,x93
                             ,x94
                             ,x95
                             ,x96
                             ,x97
                             ,x98
                             ,x99
                             ,x100
                             ,x101
                             ,x102
                             ,x103
                             ,x104
                             ,x105
                             ,x106
                             ,x107
                             ,x108
                             ,x109
                             ,x110
                             ,x111
                             ,x112
                             ,x113
                             ,x114
                             ,x115
                             ,x116
                             ,x117
                             ,x118
                             ,x119
                             ,x120
                             ,(x121
                              ,x122
                              ,x123
                              ,x124
                              ,x125
                              ,x126
                              ,x127
                              ,x128
                              ,x129
                              ,x130
                              ,x131
                              ,x132
                              ,x133
                              ,x134
                              ,x135
                              ,x136
                              ,x137
                              ,x138
                              ,x139
                              ,x140
                              ,x141
                              ,x142
                              ,x143
                              ,x144
                              ,x145
                              ,x146
                              ,x147
                              ,x148
                              ,x149
                              ,x150
                              ,x151
                              ,x152
                              ,x153
                              ,x154
                              ,x155
                              ,x156
                              ,x157
                              ,x158
                              ,x159
                              ,x160
                              ,x161
                              ,x162
                              ,x163
                              ,x164
                              ,x165
                              ,x166
                              ,x167
                              ,x168
                              ,x169
                              ,x170
                              ,x171
                              ,x172
                              ,x173
                              ,x174
                              ,x175
                              ,x176
                              ,x177
                              ,x178
                              ,x179
                              ,x180
                              ,x181
                              ,(x182
                               ,x183
                               ,x184
                               ,x185
                               ,x186
                               ,x187
                               ,x188
                               ,x189
                               ,x190
                               ,x191
                               ,x192
                               ,x193
                               ,x194
                               ,x195
                               ,x196
                               ,x197
                               ,x198))))"""
