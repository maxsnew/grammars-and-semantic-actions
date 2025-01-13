open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.FinSet
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.String.Unambiguous Alphabet
open import Term.Base Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  different-char : Grammar ℓ-zero
  different-char =
    ⊕[ c' ∈ ⟨ Alphabet ⟩ ] ⊕[ x ∈ (c Eq.≡ c' → Empty.⊥ ) ] ＂ c' ＂

  disjoint-different-char : disjoint ＂ c ＂ different-char
  disjoint-different-char =
    {!!}

  different-char→char : different-char ⊢ char
  different-char→char = ⊕ᴰ-elim (λ c' → ⊕ᴰ-elim λ _ → ⊕ᴰ-in c')

  different-char-in :
    {c' : ⟨ Alphabet ⟩} →
    (c Eq.≡ c' → Empty.⊥) →
    literal c' ⊢ different-char
  different-char-in {c'} c≢c' = ⊕ᴰ-in c' ∘g ⊕ᴰ-in c≢c'

  literal-complement : Grammar ℓ-zero
  literal-complement =
    ε ⊕
    (different-char ⊗ string) ⊕
    (＂ c ＂ ⊗ (char +))

  literal-complement-empty? : literal-complement ⊢ ε ⊕ char +
  literal-complement-empty? =
    ⊕-elim
      ⊕-inl
      (⊕-elim
        (⊕-inr ∘g different-char→char ,⊗ id)
        (⊕-inr ∘g ⊕ᴰ-in c ,⊗ +→* char)
      )

  literal→char+ : ＂ c ＂ ⊢ char +
  literal→char+ = +-singleton char ∘g ⊕ᴰ-in c


  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    is-literal? : char ⊢ ＂ c ＂ ⊕ different-char
    is-literal? = ⊕ᴰ-elim λ c' →
      decRec
        (λ {Eq.refl → ⊕-inl})
        (λ c≢c' → ⊕-inr ∘g different-char-in c≢c')
        (Discrete→dec-Eq≡ (isFinSet→Discrete isFinSetAlphabet) c c')

    opaque
      unfolding _⊕_ ε literal
      parse-literal :
        string ⊢ ＂ c ＂ ⊕ literal-complement
      parse-literal =
        rec (*Ty char)
        (λ _ → ⊕ᴰ-elim λ {
          nil → ⊕-inr ∘g ⊕-inl ∘g lowerG ∘g lowerG
        ; cons →
          ⊕-elim
            (
            ⊕-elim
              ⊕-inl
              (⊕-inr ∘g ⊕-inr ∘g ⊕-inl ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻)
            ∘g is-literal?
            ∘g ⊗-unit-r)
            (⊕-inr
            ∘g ⊕-elim
              (⊕-inr ∘g ⊕-inr)
              (⊕-inr ∘g ⊕-inl ∘g id ,⊗ +→* char)
            ∘g ⊗⊕-distR
            ∘g is-literal? ,⊗ id
            )
          ∘g ⊗⊕-distL
          ∘g id ,⊗ ⊕-elim (⊕-inr ∘g literal→char+) literal-complement-empty?
          ∘g (lowerG ,⊗ lowerG)
        })
        _

    open StrongEquivalence
    totallyParseableLiteral : totallyParseable ＂ c ＂
    totallyParseableLiteral .fst = literal-complement
    totallyParseableLiteral .snd .fun = ⊤-intro
    totallyParseableLiteral .snd .inv = parse-literal ∘g ⊤→string
    totallyParseableLiteral .snd .sec = unambiguous⊤ _ _
    totallyParseableLiteral .snd .ret = {!!}

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    unambiguous-literal : unambiguous ＂ c ＂
    unambiguous-literal = ans
      where
      opaque
        unfolding literal
        ans : unambiguous ＂ c ＂
        ans = EXTERNAL.isLang→unambiguous isFinSetAlphabet λ w → isSetString _ _
