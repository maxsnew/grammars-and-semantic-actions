open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.AsPath.Properties (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Literal.AsPath.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Unambiguous Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet

open import Term.Base Alphabet

open StrongEquivalence

module _ (c : ⟨ Alphabet ⟩) (discAlphabet : Discrete ⟨ Alphabet ⟩)  where
  -- Need the discreteness (decidable equality) of the alphabet to establish
  -- that char ≅ ＂ c ＂ ⊕ <sum over other characters>
  --
  -- In particular finite sets are discrete. So we may leverage this lemma
  -- when instantiated with a finite alphabet

  different-literal : Grammar ℓ-zero
  different-literal = ⊕[ c' ∈ ⟨ Alphabet ⟩ ] ⊕[ _ ∈ ((c ≡ c') → Empty.⊥) ] ＂ c' ＂

  module _ where
    private
      which-lit-ty : (c' : ⟨ Alphabet ⟩) → Type ℓ-zero
      which-lit-ty c' = ＂ c' ＂ ⊢ ＂ c ＂ ⊕ different-literal

      different-lit-map : (c' : ⟨ Alphabet ⟩) → (c ≡ c' → Empty.⊥) → which-lit-ty c'
      different-lit-map c' c≢c' = inr ∘g σ c' ∘g σ c≢c'

      motive : (c' : ⟨ Alphabet ⟩) → c ≡ c' → Type ℓ-zero
      motive c' _ = which-lit-ty c'

      mk-which-lit : (c' : ⟨ Alphabet ⟩) → which-lit-ty c'
      mk-which-lit c' = decRec (J motive inl) (different-lit-map c') (discAlphabet c c')

    which-literal≅ : char ≅ ＂ c ＂ ⊕ different-literal
    which-literal≅ .fun = ⊕ᴰ-elim mk-which-lit
    which-literal≅ .inv = ⊕-elim (literal→char c) (⊕ᴰ-elim λ c' → ⊕ᴰ-elim λ _ → literal→char c')
    which-literal≅ .sec = the-sec
      where
      opaque
        unfolding ⊕-elim
        the-sec : which-literal≅ .fun ∘g which-literal≅ .inv ≡ id
        the-sec =
          ⊕≡ _ _
            (decElim {P = c ≡ c}
               {A = λ x → decRec (J motive inl) (different-lit-map c) x ≡
                            inl}
               (λ c≡c → cong (J motive inl) (Alphabet .snd c c _ _) ∙ JRefl motive inl)
               (λ c≢c → Empty.rec (c≢c refl))
               (discAlphabet c c))
            (⊕ᴰ≡ _ _ λ c' → ⊕ᴰ≡ _ _ λ c≢c' →
              decElim {P = c ≡ c'}
                {A = λ x → decRec (J motive inl) (different-lit-map c') x ≡
                  inr ∘g σ c' ∘g σ c≢c'}
                (λ c≡c' → Empty.rec (c≢c' c≡c'))
                (λ c≢'c' → cong ((inr {B = ＂ c ＂} ∘g σ c') ∘g_) (cong σ (isProp→ Empty.isProp⊥ _ _)))
                (discAlphabet c c')
            )
    which-literal≅ .ret = unambiguous-char _ _

  unambiguous-literal : unambiguous ＂ c ＂
  unambiguous-literal = summand-L-is-unambig (unambiguous≅ which-literal≅ unambiguous-char)
