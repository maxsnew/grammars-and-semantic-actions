module Semantics.Term where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma

open import Semantics.Grammar
open import Semantics.String
open import Semantics.Helper

{-- Embed the linear typing rules
 -- These correspond to terms like x : g ⊢ M : g'
 -- with the caveat that derivations
 -- x : g , y : h ⊢ M : g'
 -- are represented as
 -- x : g ⊗ h ⊢ M : g'
 --
 -- Likewise, we represent the empty context with the empty grammar
 -- ∙ ⊢ M : g
 -- is given as
 -- x : ε-grammar ⊢ M : g
 --}
module _ ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  -- TODO replace FinSet with Type
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)

  Term = ParseTransformer

  id : {g : Grammar} → Term g g
  id x = x

  ε-extension-r :
    {g h k : Grammar} →
    Term g ε-grammar →
    Term h k →
    Term (h ⊗ g) k
  ε-extension-r {g = g} {k = k} e e' p =
    transport
      (cong k ((sym (++-unit-r (fst p .fst .fst)) ∙
      cong (λ a → p .fst .fst .fst ++ a) (sym (e (p .snd .snd)))) ∙
      sym (p .fst .snd)))
      (e' (p .snd .fst))

  ε-extension-l :
    {g h k : Grammar} →
    Term g ε-grammar →
    Term h k →
    Term (g ⊗ h) k
  ε-extension-l {g = g} {k = k} e e' p =
    transport
      (cong k (cong (λ a → a ++ p .fst .fst .snd) (sym (e (p .snd .fst))) ∙
        sym (p .fst .snd)))
      (e' (p .snd .snd))

  ⊗-intro :
    {g h k l : Grammar} →
    Term g h →
    Term k l →
    Term (g ⊗ k) (h ⊗ l)
  ⊗-intro e e' p =
    p .fst , (e (p .snd .fst)) , (e' (p .snd .snd))

  -⊗-intro :
    {g h k : Grammar} →
    Term (g ⊗ h) k →
    Term h (g -⊗ k)
  -⊗-intro e p w' q =
    e ((_ , refl) , (q , p))

  -⊗-elim :
    {g h k l : Grammar} →
    Term h (g -⊗ k) →
    Term l g →
    Term (l ⊗ h) k
  -⊗-elim {k = k} e e' p =
    transport (sym (cong k (p .fst .snd)))
      (e (p .snd .snd) (fst p .fst .fst) (e' (p .snd .fst)))

  ⊗--intro :
    {g h k : Grammar} →
    Term (g ⊗ h) k →
    Term g (k ⊗- h)
  ⊗--intro e p w' q =
    e ((_ , refl) , p , q)

  ⊗--elim :
    {g h k l : Grammar} →
    Term g (k ⊗- h) →
    Term l h →
    Term (g ⊗ l) k
  ⊗--elim {k = k} e e' p =
    transport
      (sym (cong k (p .fst .snd)))
      (e (p .snd .fst) (fst p .fst .snd) (e' (p .snd .snd)))

  ⊗-assoc :
    {g h k l : Grammar} →
    Term (g ⊗ h ⊗ k) l →
    Term ((g ⊗ h) ⊗ k) l
  ⊗-assoc e p =
      (e
        (((fst (p .snd .fst) .fst .fst ,
           fst (p .snd .fst) .fst .snd ++ fst p .fst .snd)
          ,
          p .fst .snd ∙
          cong (λ a → a ++ p .fst .fst .snd) (p .snd .fst .fst .snd) ∙
          ++-assoc
            (p .snd .fst .fst .fst .fst)
            (p .snd .fst .fst .fst .snd)
            (p .fst .fst .snd)) ,
        ((p .snd .fst .snd .fst) ,
        (((fst (p .snd .fst) .fst .snd , fst p .fst .snd) , refl) ,
        ((p .snd .fst .snd .snd) , (p .snd .snd))))))

  ⊗-assoc-inv :
    {g h k l : Grammar} →
    Term ((g ⊗ h) ⊗ k) l →
    Term (g ⊗ h ⊗ k) l
  ⊗-assoc-inv e p =
    e
      (((fst p .fst .fst ++ fst (p .snd .snd) .fst .fst ,
        fst (p .snd .snd) .fst .snd) ,
      p .fst .snd ∙
      sym (++-assoc
        (p .fst .fst .fst)
        (p .snd .snd .fst .fst .fst) (fst (p .snd .snd) .fst .snd) ∙
      cong (λ a → p .fst .fst .fst ++ a) (sym (p .snd .snd .fst .snd)))) ,
        ((((fst p .fst .fst , fst (p .snd .snd) .fst .fst) ,
        refl) ,
        ((p .snd .fst) , (p .snd .snd .snd .fst))) , (p .snd .snd .snd .snd)))


  -- LinearΠ-intro : {!!}
  -- LinearΠ-intro = {!!}

  -- LinearΠ-elim : {!!}
  -- LinearΠ-elim = {!!}

  -- LinearΣ-intro : {!!}
  -- LinearΣ-intro = {!!}

  -- LinearΣ-elim : {!!}
  -- LinearΣ-elim = {!!}

  ⊤-intro :
    {g : Grammar} →
    Term g ⊤-grammar
  ⊤-intro p = tt*

  ⊥-elim :
    {g : Grammar} →
    Term ⊥-grammar g
  ⊥-elim x = ⊥.elim (lower x)

  &-intro :
    {g h k : Grammar} →
    Term g h →
    Term g k →
    Term g (h & k)
  &-intro e e' p =
    e p , e' p

  &-elim₁ :
    {g h k : Grammar} →
    Term g (h & k) →
    Term g h
  &-elim₁ e p = e p .fst

  &-elim₂ :
    {g h k : Grammar} →
    Term g (h & k) →
    Term g k
  &-elim₂ e p = e p .snd

  ⊕-intro₁ :
    {g h k : Grammar} →
    Term g h →
    Term g (h ⊕ k)
  ⊕-intro₁ e p = inl (e p)

  ⊕-intro₂ :
    {g h k : Grammar} →
    Term g k →
    Term g (h ⊕ k)
  ⊕-intro₂ e p = inr (e p)

  ⊕-elim :
    {g h k : Grammar} →
    Term g k →
    Term h k →
    Term (g ⊕ h) k
  ⊕-elim eg eh p =
    Sum.elim
      (λ pg → eg pg)
      (λ ph → eh ph)
      p

  ⇒-intro :
    {g h : Grammar} →
    Term g h →
    Term ε-grammar (g ⇒ h)
  ⇒-intro e pε pg = e pg

  -- ⇒-elim : {!!}
  -- ⇒-elim = {!!}

  KL*-intro-nil :
    {g : Grammar} →
    Term ε-grammar (KL* g)
  KL*-intro-nil p =
    transport (cong₂ KL*Ty refl (sym p)) KL*Ty.nil

  KL*-intro-cons :
    {g : Grammar} →
    Term (g ⊗ KL* g) (KL* g)
  KL*-intro-cons {g = g} p =
    transport (cong (KL*Ty g) (sym (p .fst .snd)))
      (KL*Ty.cons (p .snd .fst) (p .snd .snd))

  KL*-elim :
    {g h : Grammar} →
    Term ε-grammar h →
    Term (g ⊗ h) h →
    Term (KL* g) h
  KL*-elim pε p⊗ nil = pε refl
  KL*-elim pε p⊗ (cons x p) =
    p⊗ ((_ , refl) , (x , (KL*-elim pε p⊗ p)))

  foldKL*r = KL*-elim

  foldKL*l :
    {g h : Grammar } →
    Term ε-grammar h →
    Term (h ⊗ g) h →
    Term (KL* g) h
  foldKL*l {g}{h} pε p⊗ p =
    -⊗-elim {g = h}{h = KL* g}{k = h}
      (foldKL*r {g = g} {h = h -⊗ h}
        (-⊗-intro (ε-extension-r (id {g = ε-grammar}) (id {g = h})))
        (-⊗-intro {g = h}{h = g ⊗ (h -⊗ h)}{k = h}
          (
          ⊗-assoc-inv {g = h}{h = g}{k = h -⊗ h}{l = h}
            (-⊗-elim {g = h}{h = h -⊗ h}{k = h}{l = h ⊗ g}
              (id {g = h -⊗ h}) p⊗)
            ))
        )
      pε
      ((_ , refl) , (refl , p))
