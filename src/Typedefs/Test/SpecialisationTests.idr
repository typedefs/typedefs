module Typedefs.Test.SpecialisationTests

import Specdris.Spec
import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.Backend
import Typedefs.Equality
import Typedefs.Backend.Utils
import Typedefs.Backend.Haskell
import Typedefs.Backend.Specialisation

import Data.Vect
import Data.NEList
import Data.SortedMap

import Text.PrettyPrint.WL

eitherBool : TNamedR 0
eitherBool = TName "A" (TSum [FRef "Bool" , FRef "Bool" ])

eitherBoolInt : TNamedR 0
eitherBoolInt = TName "A" (TSum [FRef "Bool" , FRef "Int" ])

-- we need to update those tests with ones that rely on TDefR instead of TDef
--export
--testSuite : IO ()
--testSuite = spec $ do
--  describe "specialisation tests" $ do
--    it "should use Bools" $
--      ((unwords . map (toString . renderDef)) <$>
--      generateTyDefs {def=Haskell} {type=HsType} [] (MkNEList (Unbounded eitherBool) []))
--        `shouldBe`
--      (pure "type A = Either Bool Bool")
--    it "should extend the context approriately" $
--      extendContext (def eitherBoolInt) specialisedTypes [] `shouldBe`
--      Right (2 **
--               ( the (TDefR 2) (TSum [RRef FZ, RRef (FS FZ)])
--               , [HsParam "Bool" [], HsParam "Int" []]))
