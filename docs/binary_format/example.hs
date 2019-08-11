module Example where

import Data.Word
import Data.ByteString.Lazy
import Data.ByteString.Builder

import Data.Void

type Serialiser a = a -> Builder

runSerialiser :: Serialiser a -> a -> ByteString
runSerialiser f = toLazyByteString . f

newtype Deserialiser a = MkDeserialiser (ByteString -> Maybe (a, ByteString))

runDeserialiser :: Deserialiser a -> ByteString -> Maybe (a, ByteString)
runDeserialiser (MkDeserialiser f) = f

instance Functor Deserialiser where
  fmap f da = MkDeserialiser (\ bs -> do
    (a, bs') <- runDeserialiser da bs
    Just (f a, bs'))

instance Applicative Deserialiser where
  pure x = MkDeserialiser (\ bs -> Just (x, bs))
  df <*> da =  MkDeserialiser (\ bs -> do
    (f, bs') <- runDeserialiser df bs
    (a, bs'') <- runDeserialiser da bs'
    Just (f a, bs''))

instance Monad Deserialiser where
  da >>= g = MkDeserialiser (\ bs -> do
    (a, bs') <- runDeserialiser da bs
    runDeserialiser (g a) bs')

failDecode :: Deserialiser a
failDecode = MkDeserialiser (\ bs -> Nothing)

deserialiseInt :: Deserialiser Integer
deserialiseInt = MkDeserialiser (\ bs -> fmap go (uncons bs))
  where go :: (Word8, ByteString) -> (Integer, ByteString)
        go (b, bs') = (toInteger b, bs')

data Boolean = True | False deriving (Show, Eq)

type Try x0 x1 = Either x0 x1

data LinkedList x0 = Nil | Cons x0 (LinkedList x0) deriving (Show, Eq)

encodeBoolean :: Serialiser Boolean
encodeBoolean Example.True = word8 (fromIntegral 0)
encodeBoolean Example.False = word8 (fromIntegral 1)

decodeBoolean :: Deserialiser Boolean
decodeBoolean = do
                  i <- deserialiseInt
                  case i of
                    0 -> return Example.True
                    1 -> return Example.False
                    _ -> failDecode

encodeTry :: Serialiser x0 -> Serialiser x1 -> Serialiser (Try x0 x1)
encodeTry encodeX0 encodeX1 x = case x of
                                  Left z -> mconcat [(word8 (fromIntegral 0))
                                                    ,(encodeX0 z)]
                                  Right z -> mconcat [(word8 (fromIntegral 1))
                                                     ,(encodeX1 z)]

decodeTry :: Deserialiser x0 -> Deserialiser x1 -> Deserialiser (Try x0 x1)
decodeTry decodeX0 decodeX1 = do
                                i <- deserialiseInt
                                case i of
                                  0 -> do
                                         y <- decodeX0
                                         return (Left y)
                                  1 -> do
                                         y0 <- decodeX1
                                         return (Right y0)
                                  _ -> failDecode

encodeLinkedList :: Serialiser x0 -> Serialiser (LinkedList x0)
encodeLinkedList encodeX0 Nil = word8 (fromIntegral 0)
encodeLinkedList encodeX0 (Cons x x0) = mconcat [(word8 (fromIntegral 1))
                                                ,(encodeX0 x)
                                                ,(encodeLinkedList encodeX0 x0)]

decodeLinkedList :: Deserialiser x0 -> Deserialiser (LinkedList x0)
decodeLinkedList decodeX0 = do
                              i <- deserialiseInt
                              case i of
                                0 -> return Nil
                                1 -> do
                                       x <- decodeX0
                                       x0 <- decodeLinkedList decodeX0
                                       return (Cons x x0)
                                _ -> failDecode
