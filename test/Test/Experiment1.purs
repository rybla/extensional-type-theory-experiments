module Test.Experiment1 where

import Prelude

import Data.Either (Either(..))
import Data.Unfoldable (none)
import Experiment1.Main (BuildDrv, Drv(..), Var(..), ann, app, assumption, lam, pi, piT, runBuildM, tactic, uni, uniT, (▹))
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

  mkTest "(λ (x : 𝒰) . (λ (y : Π 𝒰 𝒰) . ($assumption :: 𝒰)))"
    (lam uni (lam (pi uni uni) (ann uniT (tactic assumption []))))
    ( _ `shouldEqual`
        Right
          ( LamDrv { gamma: mempty, dom: uniT, cod: piT (piT uniT uniT) uniT }
              $ LamDrv { gamma: uniT ▹ mempty, dom: piT uniT uniT, cod: uniT }
              $ TacticDrv { gamma: piT uniT uniT ▹ uniT ▹ mempty, ty: uniT } assumption
              $ VarDrv { gamma: piT uniT uniT ▹ uniT ▹ mempty, ty: uniT } (Var 1)
          )
    )

  mkTest "(((λ (x : 𝒰) . x) 𝒰) :: 𝒰)"
    (ann uniT (app (lam uni (var 0)) uni))
    ( _ `shouldEqual` Right
        (UniDrv { gamma: mempty })
    )

  where
  mkTest label mdrv f = it label do
    let err_drv = runBuildM $ mdrv mempty none
    f err_drv

