module Test.Experiment1 where

import Prelude

import Data.Either (Either(..))
import Data.Newtype (wrap)
import Experiment1.Main (Ctx, Drv(..), ann, anyT, app, app', assumption, lam, lam', pi, piT, refl, runBuildM, tactic, trans, uni, uniT, var, varT, (▹))
import Test.Common (shouldEqual)
import Test.Spec (Spec, describe, it)

ε = mempty :: Ctx

spec :: Spec Unit
spec = describe "Experiment1" do

  mkTest "λ (x : 𝒰) . x"
    (lam uni (var 0))
    ( _ `shouldEqual` Right do
        Lam { gamma: ε, dom: uniT, cod: uniT } $
          Var { gamma: uniT ▹ ε, ty: uniT } (wrap 0)
    )

  mkTest "(λ (x : 𝒰) . x) 𝒰"
    (app (lam uni (var 0)) uni)
    ( _ `shouldEqual` Right do
        App { gamma: ε, dom: uniT, cod: uniT }
          ( Lam { gamma: ε, dom: uniT, cod: uniT } $
              Var { gamma: uniT ▹ ε, ty: uniT } (wrap 0)
          )
          (Uni { gamma: ε })
    )

  mkTest "λ (x : 𝒰) . ($assumption :: 𝒰)"
    (lam uni (ann (tactic assumption []) uniT))
    ( _ `shouldEqual` Right do
        Lam { gamma: ε, dom: uniT, cod: uniT }
          $ Ann { gamma: uniT ▹ ε, ty: uniT }
          $ Tactic { gamma: uniT ▹ ε, ty: uniT } assumption
          $ Var { gamma: uniT ▹ ε, ty: uniT } (wrap 0)
    )

  mkTest "λ (x : 𝒰) . λ (y : Π 𝒰 𝒰) . ($assumption :: 𝒰)"
    (lam uni (lam (pi uni uni) (ann (tactic assumption []) uniT)))
    ( _ `shouldEqual` Right do
        Lam { gamma: ε, dom: uniT, cod: piT (piT uniT uniT) uniT }
          $ Lam { gamma: uniT ▹ ε, dom: piT uniT uniT, cod: uniT }
          $ Ann { gamma: piT uniT uniT ▹ uniT ▹ ε, ty: uniT }
          $ Tactic { gamma: piT uniT uniT ▹ uniT ▹ ε, ty: uniT } assumption
          $ Var { gamma: piT uniT uniT ▹ uniT ▹ ε, ty: uniT } (wrap 1)
    )

  mkTest "trans refl 𝒰 :: 𝒰"
    (ann (trans refl uni) uniT)
    ( _ `shouldEqual` Right do
        Ann { gamma: ε, ty: uniT } $
          Trans { gamma: ε, ty0: uniT, ty1: uniT }
            (Refl { gamma: ε, ty: uniT })
            (Uni { gamma: ε })
    )

  mkTest "(λ (x : 𝒰) . x) 𝒰 :: 𝒰"
    (ann (app (lam uni (var 0)) uni) uniT)
    ( _ `shouldEqual` Right do
        Ann { gamma: ε, ty: uniT } $
          App { gamma: ε, dom: uniT, cod: uniT }
            ( Lam { gamma: ε, dom: uniT, cod: uniT } $
                Var { gamma: uniT ▹ ε, ty: uniT } (wrap 0)
            )
            (Uni { gamma: ε })
    )

  mkTest "(λ (x : 𝒰) . x) 𝒰 :: 𝒰"
    (ann (app (lam uni (var 0)) uni) uniT)
    ( _ `shouldEqual` Right do
        Ann { gamma: ε, ty: uniT } $
          App { gamma: ε, dom: uniT, cod: uniT }
            ( Lam { gamma: ε, dom: uniT, cod: uniT } $
                Var { gamma: uniT ▹ ε, ty: uniT } (wrap 0)
            )
            (Uni { gamma: ε })
    )

  mkTest "(λ (A : 𝒰) . λ (x : A#0) . x#0) 𝒰 𝒰 :: 𝒰"
    (app' (lam' [ uni, var 0 ] (var 0)) [ uni, uni ] `ann` uniT)
    ( _ `shouldEqual` Right do
        Ann { gamma: ε, ty: uniT } $
          App { gamma: ε, dom: uniT, cod: uniT }
            ( App { gamma: ε, dom: uniT, cod: piT uniT uniT }
                ( Lam { gamma: ε, dom: uniT, cod: piT (varT 0) (varT 1) }
                    $ Lam { gamma: uniT ▹ ε, dom: varT 0, cod: varT 1 }
                    $ Var { gamma: varT 0 ▹ uniT ▹ ε, ty: varT 1 } (wrap 0)
                )
                (Uni { gamma: ε })
            )
            (Uni { gamma: ε })
    )

  where
  mkTest label mdrv f = it label do
    let err_drv = runBuildM $ mdrv ε anyT
    f err_drv

