
-- $ agda --ghc Main.agda
-- $ ./Main

{-# OPTIONS --guardedness #-}
module Main where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.String

open import Level
open import Data.Unit.Polymorphic
open import Effect.Monad
open import IO

import Meta.Export as Export
import Meta.Show   as Show

open import Examples.Simple
open import Examples.Poseidon2
open import Examples.Tests
open import Examples.IOExample

--------------------------------------------------------------------------------

exStr1 : String
exStr1 = Export.exportToString exIO0b -- exClosure1 -- exRecMul -- exMontInv -- exModInv -- exInvU64xy -- exBabyModInv --exTinyModInv -- exIO1 -- Big.exBinary -- natEx2 -- exMont2b  -- myApplication  -- exBigMul  -- exMod1 -- exSmall1 -- myApplication

-- letFunTest -- liftTest1 -- myApplication -- small2 -- exMont2 -- mixedLam1 -- lamEx2a -- exMod1 -- natEx2 

--------------------------------------------------------------------------------

sanityCheckMontgomery : IO {0ℓ} ⊤
sanityCheckMontgomery = do
  putStrLn Examples.Simple.Bar.MontP.sanityCheckMontgomeryText


main : Main
main = run do
  -- sanityCheckMontgomery
  putStrLn exStr1

--------------------------------------------------------------------------------

