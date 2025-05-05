{-# OPTIONS --guardedness #-}
module Test where

open import Data.String.Base
open import IO

postulate
  error : String

main : Main
main = run do
  putStrLn error
