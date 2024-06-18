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

open import Cubical.HITs.PropositionalTruncation

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
module TermDefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  -- TODO replace FinSet with Type
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)

  id : {g : Grammar} → Term g g
  id x = x

  trans :
    {g h k : Grammar} →
    Term g h →
    Term h k →
    Term g k
  trans e e' p = e' (e p)

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

  ε-contraction-l :
    {g h k : Grammar} →
    Term ε-grammar g →
    Term (g ⊗ h) k →
    Term h k
  ε-contraction-l {g = g} {k = k} e e' p =
    e' ((([] , _) , refl) , (e refl , p))

  ε-contraction-r :
    {g h k : Grammar} →
    Term ε-grammar g →
    Term (h ⊗ g) k →
    Term h k
  ε-contraction-r {g = g} {k = k} e e' p =
    e' (((_ , []) , sym (++-unit-r _)) , (p , e refl))

  ⊗-intro :
    {g h k l : Grammar} →
    Term g h →
    Term k l →
    Term (g ⊗ k) (h ⊗ l)
  ⊗-intro e e' p =
    p .fst , (e (p .snd .fst)) , (e' (p .snd .snd))

  ⊗-elim :
    {g h k l : Grammar} →
    Term g (h ⊗ k) →
    Term (h ⊗ k) l →
    Term g l
  ⊗-elim e e' p =
    let (s , ph , pk) = e p in
    e' (s , (ph , pk))

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

  LinearΠ-intro :
    {A : Type ℓ} → {f : A → Grammar} →
    {g : Grammar} →
    (∀ a → Term g (f a)) →
    Term g (LinearΠ f)
  LinearΠ-intro e p a = e a p

  LinearΠ-elim :
    {A : Type ℓ} → {f : A → Grammar} →
    {g : Grammar} →
    Term g (LinearΠ f) →
    (a : A) →
    Term g (f a)
  LinearΠ-elim e a p = e p a

  LinearΣ-intro :
    {A : Type ℓ} → {f : A → Grammar} →
    {g : Grammar} →
    (a : A) →
    Term g (f a) →
    Term g (LinearΣ f)
  LinearΣ-intro a e p = a , (e p)

  LinearΣ-elim :
    {A : Type ℓ} → {f : A → Grammar} →
    {g h : Grammar} →
    Term g (LinearΣ f) →
    (∀ a → Term (f a) h) →
    Term g h
  LinearΣ-elim e e' p =
    let (a , b) = e p in
    e' a b

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

  Maybe-yes-intro :
    {g h : Grammar} →
    Term g h →
    Term g (Maybe h)
  Maybe-yes-intro {g}{h} p = ⊕-intro₁ {g = g} {h = h} {k = ⊤-grammar} p

  Maybe-no-intro :
    {g h : Grammar} →
    Term g (Maybe h)
  Maybe-no-intro {g}{h} = ⊕-intro₂ {g = g} {h = h} {k = ⊤-grammar} (⊤-intro {g = g})

  Maybe-elim :
    {g h : Grammar} →
    Term g h →
    Term ⊤-grammar h →
    Term (Maybe g) h
  Maybe-elim = ⊕-elim

  Maybe-return :
    {g h : Grammar} →
    Term g h →
    Term g (Maybe h)
  Maybe-return = Maybe-yes-intro

  Maybe-bind :
    {g h : Grammar} →
    Term g (Maybe h) →
    Term (Maybe g) (Maybe h)
  Maybe-bind {g} {h} p = Maybe-elim {g = g} {h = Maybe h} p (Maybe-no-intro {g = ⊤-grammar} {h = h})


  DecProp-grammar'-intro :
    (d : DecProp ℓ) →
    {g : Grammar} →
    Term
      g
      (DecProp-grammar' d ⊕ DecProp-grammar' (negateDecProp d))
  DecProp-grammar'-intro (a , yes x) {g} p =
    ⊕-intro₁
      {g = g}
      {h = DecProp-grammar' ((a , yes x))}
      {k = DecProp-grammar' (negateDecProp (a , yes x))}
      (⊤-intro {g = g})
      p
  DecProp-grammar'-intro (a , no ¬x) {g} p =
    ⊕-intro₂
      {g = g}
      {h = DecProp-grammar' ((a , no ¬x))}
      {k = DecProp-grammar' (negateDecProp (a , no ¬x))}
      (⊤-intro {g = g})
      p

  ⇒-intro :
    {g h : Grammar} →
    Term g h →
    Term ε-grammar (g ⇒ h)
  ⇒-intro e pε pg = e pg

  -- TODO what should the implication elim be?
  -- ⇒-elim : {!!}
  -- ⇒-elim = {!!}

  KL*-elim :
    {g h : Grammar} →
    Term ε-grammar h →
    Term (g ⊗ h) h →
    Term (KL* g) h
  KL*-elim pε p⊗ (nil x) = pε x
  KL*-elim {g}{h} pε p⊗ (cons x) =
    p⊗ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ (x .snd .snd))))

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

  ∥∥grammar-intro :
    {g : Grammar} →
    Term g (∥ g ∥grammar)
  ∥∥grammar-intro {g} p = ∣ p ∣₁

  ∥∥grammar-elim :
    {g h : Grammar} →
    isPropValuedGrammar h →
    Term g h →
    Term (∥ g ∥grammar) h
  ∥∥grammar-elim isProph e p =
    Cubical.HITs.PropositionalTruncation.elim
    (λ _ → isProph)
    (λ pg → e pg)
    p
