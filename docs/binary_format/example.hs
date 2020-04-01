module Example where

import Data.Word
import Data.ByteString.Lazy
import Data.ByteString.Builder

import Data.Void

type Cerealiser a = a -> Builder

runCerealiser :: Cerealiser a -> a -> ByteString
runCerealiser f = toLazyByteString . f

newtype PourMilk a = MkPourMilk (ByteString -> Maybe (a, ByteString))

runPourMilk :: PourMilk a -> ByteString -> Maybe (a, ByteString)
runPourMilk (MkPourMilk f) = f

instance Functor PourMilk where
  fmap f da = MkPourMilk (\ bs -> do
    (a, bs') <- runPourMilk da bs
    Just (f a, bs'))

instance Applicative PourMilk where
  pure x = MkPourMilk (\ bs -> Just (x, bs))
  df <*> da =  MkPourMilk (\ bs -> do
    (f, bs') <- runPourMilk df bs
    (a, bs'') <- runPourMilk da bs'
    Just (f a, bs''))

instance Monad PourMilk where
  da >>= g = MkPourMilk (\ bs -> do
    (a, bs') <- runPourMilk da bs
    runPourMilk (g a) bs')

failDecode :: PourMilk a
failDecode = MkPourMilk (\ bs -> Nothing)

pourmilkInt :: PourMilk Integer
pourmilkInt = MkPourMilk (\ bs -> fmap go (uncons bs))
  where go :: (Word8, ByteString) -> (Integer, ByteString)
        go (b, bs') = (toInteger b, bs')

data Boolean = True | False deriving (Show, Eq)

type Try x0 x1 = Either x0 x1

data LinkedList x0 = Nil | Cons x0 (LinkedList x0) deriving (Show, Eq)

encodeBoolean :: Cerealiser Boolean
encodeBoolean Example.True = word8 (fromIntegral 0)
encodeBoolean Example.False = word8 (fromIntegral 1)

decodeBoolean :: PourMilk Boolean
decodeBoolean = do
                  i <- pourmilkInt
                  case i of
                    0 -> return Example.True
                    1 -> return Example.False
                    _ -> failDecode

encodeTry :: Cerealiser x0 -> Cerealiser x1 -> Cerealiser (Try x0 x1)
encodeTry encodeX0 encodeX1 x = case x of
                                  Left z -> mconcat [(word8 (fromIntegral 0))
                                                    ,(encodeX0 z)]
                                  Right z -> mconcat [(word8 (fromIntegral 1))
                                                     ,(encodeX1 z)]

decodeTry :: PourMilk x0 -> PourMilk x1 -> PourMilk (Try x0 x1)
decodeTry decodeX0 decodeX1 = do
                                i <- pourmilkInt
                                case i of
                                  0 -> do
                                         y <- decodeX0
                                         return (Left y)
                                  1 -> do
                                         y0 <- decodeX1
                                         return (Right y0)
                                  _ -> failDecode

encodeLinkedList :: Cerealiser x0 -> Cerealiser (LinkedList x0)
encodeLinkedList encodeX0 Nil = word8 (fromIntegral 0)
encodeLinkedList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                                ,(encodeX0 x)
                                                ,(encodeLinkedList encodeX0 x0)]

decodeLinkedList :: PourMilk x0 -> PourMilk (LinkedList x0)
decodeLinkedList decodeX0 = do
                              i <- pourmilkInt
                              case i of
                                0 -> return Nil
                                1 -> do
                                       x <- decodeX0
                                       x0 <- decodeLinkedList decodeX0
                                       return (Cons x x0)
                                _ -> failDecode
