module Typedefs.Test.TermParseWriteTests

import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Names
import Typedefs.TermParse
import Typedefs.TermWrite

import Data.Vect
import Data.Bytes
import Data.ByteArray
import TParsec
import Specdris.Spec

%access public export

roundtrip1 : (td : TDefR 0) -> Ty [] td -> Maybe ((Ty [] td), Bytes)
roundtrip1 td x = pourmilkBinaryClosed td $ cerealiseBinaryClosed td x

roundtrip2 : (td : TDefR 0) -> Bytes -> Maybe Bytes
roundtrip2 td b = map (cerealiseBinaryClosed td . fst) (pourmilkBinaryClosed td b)

testSuite : IO ()
testSuite = spec $ do

  describe "TermWrite" $ do

    it "cerealise unit" $
      (cerealise [] [] T1 ()) `shouldBe` "()"

    it "cerealise sum" $
      (cerealise [] [] (TSum [T1, T1]) (Left ())) `shouldBe` "(left ())"

    it "cerealise prod with var" $
      (cerealise [Integer] [show] (TProd [T1, TVar 0]) ((), 2)) `shouldBe` "(both () 2)"

    it "cerealise mu" $
      (cerealise [Integer] [show] TList (Inn $ Right (1, Inn $ Right (2, Inn $ Left ()))))
      `shouldBe`
      "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))"

    it "cerealise nested mu" $
      (cerealise [] [] (TList `ap` [TNat]) (fromList {tdef=TNat} $ map fromNat [3,2,1]))
        `shouldBe`
      ("(inn (right (both (inn (right (inn (right (inn (right (inn (left ())))))))) " ++
       "(inn (right (both (inn (right (inn (right (inn (left ())))))) " ++
       "(inn (right (both (inn (right (inn (left ())))) (inn (left ())))))))))))")

    it "cerealise doubly nested mu specified via partial application" $
      (cerealise [] [] ((TList `ap` [TList]) `ap` [TNat]) (fromList {tdef=TList `ap` [TNat]} (map (fromList {tdef=TNat} . map fromNat) [[1],[2]])))
        `shouldBe`
      ("(inn (right (both (inn (right (both (inn (right (inn (left ())))) (inn (left ()))))) " ++
       "(inn (right (both (inn (right (both (inn (right (inn (right (inn (left ())))))) (inn (left ()))))) (inn (left ()))))))))")

  describe "TermParse" $ do

    it "pourmilk unit" $
      (pourmilk [] [] T1 "()") `shouldBe` (Just ())

    it "pourmilk sum" $
      (pourmilk [] [] (TSum [T1, T1]) "(left ())") `shouldBe` (Just (Left ()))

    it "pourmilk prod with var" $
      (pourmilk [Integer] [decimalInteger] (TProd [T1, TVar 0]) "(both () 2)") `shouldBe` (Just ((), 2))

--    it "pourmilk mu" $
--      (pourmilk [Integer] [decimalInteger] (TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]) "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))")
--      `shouldBe`
--      (Just (Inn (Right (1, Inn (Right (2, Inn (Left ())))))))

    it "pourmilk nested mu" $
      (pourmilk [] [] (TList `ap` [TNat])
        ("(inn (right (both (inn (right (inn (right (inn (right (inn (left ())))))))) " ++
         "(inn (right (both (inn (right (inn (right (inn (left ())))))) " ++
         "(inn (right (both (inn (right (inn (left ())))) (inn (left ())))))))))))"))
        `shouldBe`
      (Just $ fromList {tdef=TNat} $ map fromNat [3,2,1])

    it "pourmilk doubly nested mu specified via partial application" $
      (pourmilk [] [] ((TList `ap` [TList]) `ap` [TNat])
        ("(inn (right (both (inn (right (both (inn (right (inn (left ())))) (inn (left ()))))) " ++
         "(inn (right (both (inn (right (both (inn (right (inn (right (inn (left ())))))) (inn (left ()))))) (inn (left ()))))))))"))
        `shouldBe`
       (Just $ fromList {tdef=TList `ap` [TNat]} (map (fromList {tdef=TNat} . map fromNat) [[1],[2]]))

{-
  describe "Binary cerealisation/decerealisation" $ do

    it "round1 unit" $ roundtrip1 T1 () `shouldBe` (Just ((), empty))

    it "round1 sum" $ roundtrip1 (TSum [T1, T1]) (Right ())  `shouldBe` (Just ((Right ()), empty))

    it "round1 prod" $ roundtrip1 (TProd [T1, T1]) ((), ())  `shouldBe` (Just (((), ()), empty))

    it "round1 mu base" $ roundtrip1 (TMu [("Nil", T1), ("Cons", TProd [(TMu [("Z", T1), ("S", TVar 0)]), TVar 0])]) (Inn (Left ()))
      `shouldBe` (Just ((Inn (Left ())), empty))

    it "round1 mu step" $ roundtrip1 (TMu [("Nil", T1), ("Cons", TProd [(TMu [("Z", T1), ("S", TVar 0)]), TVar 0])]) (Inn (Right ((Inn (Left ()), Inn (Right ((Inn (Right (Inn (Left ()))), Inn (Right ((Inn (Right (Inn (Right (Inn (Left ()))))), Inn (Left ())))))))))))
      `shouldBe` (Just ((Inn (Right ((Inn (Left ()), Inn (Right ((Inn (Right (Inn (Left ()))), Inn (Right ((Inn (Right (Inn (Right (Inn (Left ()))))), Inn (Left ()))))))))))), empty))
-}
