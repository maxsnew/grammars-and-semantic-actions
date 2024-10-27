module SemanticAction.CSV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Empty renaming (⊥ to EmptyType)
open import Cubical.Data.List as List
open import Cubical.Data.Sigma

open import String.Unicode
open import Grammar Unicode
open import Term Unicode
open import SemanticAction.Base Unicode

module Concrete where
  isQuotedChar : ⟨ Unicode ⟩ → Type ℓ-zero
  isQuotedChar c = c ≡ '"' → EmptyType

  QuotedLit : Grammar ℓ-zero
  QuotedLit =
    (⊕[ (c , _ ) ∈ Σ ⟨ Unicode ⟩ isQuotedChar ] literal c)
    ⊕ (literal '"' ⊗ literal '"')

  QuotedField : Grammar ℓ-zero
  QuotedField = KL* QuotedLit

  isUnquotedChar : ⟨ Unicode ⟩ → Type ℓ-zero
  isUnquotedChar c =
    (c ≡ ',' → EmptyType)
    × (c ≡ '"' → EmptyType)
    × (c ≡ '\n' → EmptyType)

  UnquotedLit : Grammar ℓ-zero
  UnquotedLit = ⊕[ (c , _) ∈ Σ ⟨ Unicode ⟩ isUnquotedChar ] literal c

  UnquotedField : Grammar ℓ-zero
  UnquotedField = KL* UnquotedLit

  Field : Grammar ℓ-zero
  Field = UnquotedField ⊕ (literal '"' ⊗ QuotedField ⊗ literal '"')

  EOL : Grammar ℓ-zero
  EOL = literal '\n'

  NonemptyLine : Grammar ℓ-zero
  NonemptyLine = Field ⊗ KL* (literal ',' ⊗ Field)

  Line : Grammar ℓ-zero
  Line = (ε ⊕ NonemptyLine) ⊗ EOL

CST : Grammar ℓ-zero
CST = KL* Concrete.Line

parser : string ⊢ CST
parser = {!!}

module Abstract where
  Field : Type ℓ-zero
  Field = List UnicodeChar

  Line : Type ℓ-zero
  Line = List Field

module Concrete→Abstract where
  quotedLit : SemanticAction Concrete.QuotedLit String
  quotedLit = semact-⊕ semact-underlying (semact-pure [ '"' ])

  quotedField : SemanticAction Concrete.QuotedField Abstract.Field
  quotedField = semact-map (List.foldl _++_ []) (semact-* quotedLit)

  field' : SemanticAction Concrete.Field Abstract.Field
  field' = semact-⊕ semact-underlying (semact-surround quotedField)

  nonemptyLine : SemanticAction Concrete.NonemptyLine Abstract.Line
  nonemptyLine =
    semact-map (uncurry _∷_) (semact-concat field'
      (semact-* (semact-right field')))

  line : SemanticAction Concrete.Line Abstract.Line
  line = semact-left (semact-⊕ (semact-pure []) nonemptyLine)

