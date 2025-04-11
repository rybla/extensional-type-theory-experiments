module Main where

import Prelude

import Effect (Effect)
import Effect.Exception (throw)
import Experiment1.Main as Experiment1

main :: Effect Unit
main = case "Experiment1" of
  "Experiment1" -> Experiment1.main
  name -> throw $ "unrecognized main name: " <> show name

