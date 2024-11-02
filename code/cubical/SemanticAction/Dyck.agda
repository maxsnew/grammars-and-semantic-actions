module SemanticAction.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.List as List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Examples.Indexed.Dyck as Dyck hiding (parser)

open import Grammar Dyck.Alphabet
open import Term Dyck.Alphabet
open import SemanticAction.Base Dyck.Alphabet
open import Test Dyck.Alphabet


data Tree : Type ℓ-zero where
  Node : (children : List Tree) → Tree


parenTree : SemanticAction IndDyck (List Tree)
parenTree =
  semact-rec (λ tt → ⊕ᴰ-elim λ where
    nil' → ⊸-elim-ε (semact-pure [])
    balanced' → ⊸-elim-ε (
      semact-right (semact-map
        (uncurry _∷_)
        (semact-concat
          (semact-map Node (semact-lift semact-Δ))
          (semact-right (semact-lift semact-Δ)))))
  ) tt


parser : string ⊢ Δ (List Tree ⊎ Unit)
parser = ⊸-elim-ε (semact-disjunct parenTree semact-⊤) ∘g Dyck.parser

module Tests where
  open Dyck using ([; ])

  s1 : String
  s1 = [ ∷ ] ∷ [ ∷ [ ∷ ] ∷ ] ∷ []

  s1-parse : List Tree ⊎ Unit
  s1-parse = runParserΔ parser s1

  _ = {!s1-parse!}

