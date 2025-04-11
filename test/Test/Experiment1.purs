module Test.Experiment1 where

import Prelude

import Data.Either (Either(..))
import Data.Tuple.Nested ((/\))
import Experiment1.Main (Drv(..), Var(..), BuildDrv, ann, app, assumption, lam, runBuildM, tactic, uni, uniT, (▹))
import Experiment1.Main as Lang
import Test.Common (shouldEqual)
import Test.Spec (Spec, describe, it)

var ∷ Int → BuildDrv
var x = Lang.var (Var x)

spec :: Spec Unit
spec = describe "Experiment1" do
  mkTest "(λ (x : 𝒰) . x)"
    (lam uni (var 0))
    ( _ `shouldEqual`
        Right
          ( LamDrv { gamma: mempty, dom: uniT, cod: uniT } $
              VarDrv { gamma: uniT ▹ mempty, ty: uniT } (Var 0)
          )
    )
  mkTest "((λ (x : 𝒰) . x) 𝒰)"
    (app (lam uni (var 0)) uni)
    ( _ `shouldEqual`
        Right
          ( AppDrv { gamma: mempty, dom: uniT, cod: uniT }
              ( LamDrv { gamma: mempty, dom: uniT, cod: uniT } $
                  VarDrv { gamma: uniT ▹ mempty, ty: uniT } (Var 0)
              )
              (UniDrv { gamma: mempty })
          )
    )
  mkTest "(λ (x : 𝒰) . ($assumption :: 𝒰))"
    (lam uni (ann uniT (tactic assumption [])))
    ( _ `shouldEqual`
        Right
          ( LamDrv { gamma: mempty, dom: uniT, cod: uniT }
              $ TacticDrv { gamma: uniT ▹ mempty, ty: uniT } assumption
              $ VarDrv { gamma: uniT ▹ mempty, ty: uniT } (Var 0)
          )
    )

  where
  mkTest label mdrv f = it label do
    let (err_drv /\ _logs) /\ _env = runBuildM mdrv
    f err_drv

