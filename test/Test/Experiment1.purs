module Test.Experiment1 where

import Prelude

import Control.Plus (empty)
import Data.Either (Either(..), isLeft, isRight)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple.Nested ((/\))
import Experiment1.Main (Ctx(..), Drv(..), Goal(..), Tactic(..), Term(..), Var(..), ann, app, assumption, lam, runBuildM, tactic, throwError_BuildM, uni, uniT, (▹))
import Experiment1.Main as Lang
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)

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
  mkTest "(λ (x : 𝒰) . (assumption! :: 𝒰))"
    (lam uni (ann uniT (tactic assumption [])))
    ( _ `shouldEqual`
        Right
          ( LamDrv { gamma: mempty, dom: uniT, cod: uniT } $
              VarDrv { gamma: uniT ▹ mempty, ty: uniT } (Var 0)
          )
    )

  where
  mkTest label mdrv f = it label do
    let (err_drv /\ _logs) /\ _env = runBuildM mdrv
    f err_drv

