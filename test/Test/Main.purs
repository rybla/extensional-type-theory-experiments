module Test.Main where

import Prelude

import Effect (Effect)
import Test.Experiment1 as Test.Experiment1
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Test.Experiment1.spec

