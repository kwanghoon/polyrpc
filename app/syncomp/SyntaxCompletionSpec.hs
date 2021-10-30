module SyntaxCompletionSpec where

import SyntaxCompletion (computeCand)
import SynCompInterface
import Test.Hspec

import System.IO (readFile)

spec = hspec $ do
  describe "syntax complection polyrpc/app/syncomp" $ do
    let tc1 = "f : Int = (2 + 3"
    it ("[tc1.sb:simple] " ++ tc1) $ do
      results <- computeCand False tc1 "" True
      results `shouldBe` [Candidate ""]

    it ("[tc1.sb:nested] " ++ tc1) $ do
      results <- computeCand False tc1 "" False
      results `shouldBe` []



