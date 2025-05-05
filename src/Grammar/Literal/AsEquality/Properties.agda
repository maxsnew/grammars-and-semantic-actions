{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.AsEquality.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

import Erased.Data.Empty as Empty
open import Erased.Relation.Nullary.Base
open import Erased.Lift.Base
open import Erased.Data.List
open import Cubical.Relation.Nullary.DecidablePropositions.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet
-- open import Grammar.String.Base Alphabet isSetAlphabet
-- open import Grammar.String.Properties Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Sum.Unambiguous Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet isSetAlphabet

open import Term.Base Alphabet isSetAlphabet

open StrongEquivalence

module _ (c : Alphabet) (discAlphabet : Discrete Alphabet)  where
  -- Need the discreteness (decidable equality) of the alphabet to establish
  -- that char ≅ ＂ c ＂ ⊕ <sum over other characters>
  --
  -- In particular finite sets are discrete. So we may leverage this lemma
  -- when instantiated with a finite alphabet

  different-literal : Grammar ℓ-zero
  different-literal = ⊕[ c' ∈ Alphabet ] ⊕[ _ ∈ ((c ≡ c') → Empty.⊥) ] ＂ c' ＂

  -- module _ where
  --   private
  --     which-lit-ty : (c' : Alphabet) → Type ℓ-zero
  --     which-lit-ty c' = ＂ c' ＂ ⊢ ＂ c ＂ ⊕ different-literal

  --     different-lit-map : (c' : Alphabet) → (c ≡ c' → Empty.⊥) → which-lit-ty c'
  --     different-lit-map c' c≢c' = inr ∘g σ c' ∘g σ c≢c'

  --     motive : (c' : Alphabet) → c ≡ c' → Type ℓ-zero
  --     motive c' _ = which-lit-ty c'

  --     mk-which-lit : (c' : Alphabet) → which-lit-ty c'
  --     mk-which-lit c' = decRec (J motive inl) (different-lit-map c') (discAlphabet c c')

  --   which-literal≅ : char ≅ ＂ c ＂ ⊕ different-literal
  --   which-literal≅ .fun = ⊕ᴰ-elim mk-which-lit
  --   which-literal≅ .inv = ⊕-elim (literal→char c) (⊕ᴰ-elim λ c' → ⊕ᴰ-elim λ _ → literal→char c')
  --   which-literal≅ .sec = the-sec
  --     where
  --     opaque
  --       unfolding ⊕-elim
  --       the-sec : which-literal≅ .fun ∘g which-literal≅ .inv ≡ id
  --       the-sec =
  --         ⊕≡ _ _
  --           (decElim {P = c ≡ c}
  --              {A = λ x → decRec (J motive inl) (different-lit-map c) x ≡
  --                           inl}
  --              (λ c≡c → cong (J motive inl) (isSetAlphabet c c _ _) ∙ JRefl motive inl)
  --              (λ c≢c → Empty.rec (c≢c refl))
  --              (discAlphabet c c))
  --           (⊕ᴰ≡ _ _ λ c' → ⊕ᴰ≡ _ _ λ c≢c' →
  --             decElim {P = c ≡ c'}
  --               {A = λ x → decRec (J motive inl) (different-lit-map c') x ≡
  --                 inr ∘g σ c' ∘g σ c≢c'}
  --               (λ c≡c' → Empty.rec (c≢c' c≡c'))
  --               (λ c≢'c' → cong ((inr {B = ＂ c ＂} ∘g σ c') ∘g_) (cong σ (isProp→ Empty.isProp⊥ _ _)))
  --               (discAlphabet c c')
  --           )
  --   which-literal≅ .ret = unambiguous-char _ _

  -- @0 unambiguous-literal : unambiguous ＂ c ＂
  -- unambiguous-literal = summand-L-is-unambig (unambiguous≅ which-literal≅ unambiguous-char)

import Grammar.Literal.AsPath.Base Alphabet isSetAlphabet as LiteralPath

private
  variable
    c : Alphabet
    ℓ : Level

module @0 _ where
  opaque
    unfolding LiteralPath.literal literal

    literal≡ : ∀ c → LiteralPath.literal c ≡ literal c
    literal≡ c = funExt λ _ → Eq.PathPathEq

    literal*≡ : ∀ c → LiteralPath.literal* {ℓ = ℓ} c ≡ literal* c
    literal*≡ c = funExt λ x → cong Lift (funExt⁻ (literal≡ c) x)

    isLangLiteral : ∀ c → isLang ＂ c ＂
    isLangLiteral c = subst isLang (literal≡ c) (LiteralPath.isLangLiteral c)

    isLangLiteral* : ∀ c → isLang (literal* {ℓ = ℓ} c)
    isLangLiteral* c = subst isLang (literal*≡ c) (LiteralPath.isLangLiteral* c)

    isLangLiteral≡ : ∀ c i → isLang (literal≡ c i)
    isLangLiteral≡ c i = subst-filler isLang (literal≡ c) (LiteralPath.isLangLiteral c) i

    isLangLiteral*≡ : ∀ c i → isLang (literal*≡ {ℓ = ℓ} c i)
    isLangLiteral*≡ c i = subst-filler isLang (literal*≡ c) (LiteralPath.isLangLiteral* c) i

    lit-intro≡ : ∀ {c} → PathP (λ i → literal≡ c i [ c ]) (LiteralPath.lit-intro {c = c}) lit-intro
    lit-intro≡ {c = c} = isProp→PathP (λ i → isLangLiteral≡ c i [ c ]) _ _

    lit*-intro≡ : ∀ {c} → PathP (λ i → literal*≡ c i [ c ]) (LiteralPath.lit*-intro {ℓ = ℓ} {c = c}) lit*-intro
    lit*-intro≡ {c = c} = isProp→PathP (λ i → isLangLiteral*≡ c i [ c ]) _ _
