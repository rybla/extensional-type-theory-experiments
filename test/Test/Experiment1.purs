module Test.Experiment1 where

import Experiment1.Main
import Prelude

import Data.Either (isLeft)
import Data.Tuple.Nested ((/\))
import Test.Spec (Spec)
import Test.Spec as Spec
import Test.Spec.Assertions (shouldSatisfy)

spec :: Spec Unit
spec = Spec.describe "Experiment1" do

  Spec.it "ex1" do
    let (err_drv /\ logs) /\ _env = runBuildM $ lam uni (var (Var 0))
    shouldSatisfy err_drv isLeft
    shouldSatisfy logs (_ == [])

  pure unit

assumption :: Tactic
assumption = Tactic
  { name: "assumption"
  , call: \{ gamma, mb_goal, args } -> throwError_BuildM $ "unimplemented"
  }

