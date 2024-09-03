open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.DFA.Decider ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
open import Semantics.DFA.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module _ (D : DFA {ℓD}) where
  open DFA

  private
    module D = DFA D
    module ¬D = DFA (negate D)

  RunFromState : (q : ⟨ D .Q ⟩) → KL* ⊕Σ₀ ⊢ (D.Parse q ⊕ ¬D.Parse q)
  RunFromState q =
    -- foldKL*l ⊕Σ₀ the-alg
    {!!}
    where
    open *l-Algebra
    the-alg : *l-Algebra ⊕Σ₀
    the-alg .the-ℓ = ℓD
    the-alg .G = D.Parse q ⊕ ¬D.Parse q
    the-alg .nil-case =
      decRec
        (λ qAcc → ⊕-inl ∘g D.nil qAcc)
        (λ ¬qAcc → ⊕-inr ∘g ¬D.nil ¬qAcc)
        (D .isAcc q .snd)
    the-alg .snoc-case = {!!}
    -- foldKL*r ⊕Σ₀ the-alg
    -- where
    -- open Algebra
    -- the-DFA-alg : Algebra D
    -- the-DFA-alg .the-ℓs = _
    -- the-DFA-alg .G q = Parse D q ⊕ Parse (negate D) q
    -- the-DFA-alg .nil-case acc = ⊕-inl ∘g nil acc
    -- the-DFA-alg .cons-case q c =
    --   ⊕-elim
    --     (⊕-inl {g = D.Parse q}{h = ¬D.Parse q} ∘g D.cons q c)
    --     (⊕-inr {g = ¬D.Parse q}{h = D.Parse q} ∘g ¬D.cons q c)
    --     ∘g
    --   ⊗-dist-over-⊕
    --     {g = literal c}
    --     {h = D.Parse (D.δ q c)}
    --     {k = ¬D.Parse (¬D.δ q c)}

    -- the-¬DFA-alg : Algebra (negate D)
    -- the-¬DFA-alg .the-ℓs = _
    -- the-¬DFA-alg .G q = Parse D q ⊕ Parse (negate D) q
    -- the-¬DFA-alg .nil-case acc = ⊕-inr ∘g nil acc
    -- the-¬DFA-alg .cons-case q c =
    --   ⊕-elim
    --     (⊕-inl {g = D.Parse q}{h = ¬D.Parse q} ∘g D.cons q c)
    --     (⊕-inr {g = ¬D.Parse q}{h = D.Parse q} ∘g ¬D.cons q c)
    --     ∘g
    --   ⊗-dist-over-⊕
    --     {g = literal c}
    --     {h = D.Parse (D.δ q c)}
    --     {k = ¬D.Parse (¬D.δ q c)}

    -- open *r-Algebra
    -- the-alg : *r-Algebra ⊕Σ₀
    -- the-alg .the-ℓ = ℓD
    -- the-alg .G = LinΣ[ q' ∈ ⟨ D.Q ⟩ ] (D.Parse q' ⊕ ¬D.Parse q')
    -- the-alg .nil-case =
    --   decRec
    --     (λ qAcc → λ w pε → q , the-DFA-alg .nil-case qAcc w pε)
    --     (λ ¬qAcc → λ w pε → q , the-¬DFA-alg .nil-case ¬qAcc w pε)
    --     (D .isAcc q .snd)
    -- the-alg .cons-case w (sp , x , (q' , p)) =
    --   (D.δ q' (x .fst)) ,
    --   the-DFA-alg .cons-case (D.δ q' (x .fst)) (x .fst) _ (sp , ((x .snd) , {!p!}))
