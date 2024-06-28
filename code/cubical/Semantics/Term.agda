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
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)

  id : {g : Grammar} → g ⊢ g
  id x = x

  ε-extension-r :
    {g h k : Grammar} →
    g ⊢ ε-grammar →
    h ⊢ k →
    h ⊗ g ⊢ k
  ε-extension-r {g = g} {k = k} e e' p =
    transport
      (cong k ((sym (++-unit-r (fst p .fst .fst)) ∙
      cong (λ a → p .fst .fst .fst ++ a) (sym (e (p .snd .snd)))) ∙
      sym (p .fst .snd)))
      (e' (p .snd .fst))

  ε-extension-l :
    {g h k : Grammar} →
    g ⊢ ε-grammar →
    h ⊢ k →
    g ⊗ h ⊢ k
  ε-extension-l {g = g} {k = k} e e' p =
    transport
      (cong k (cong (λ a → a ++ p .fst .fst .snd) (sym (e (p .snd .fst))) ∙
        sym (p .fst .snd)))
      (e' (p .snd .snd))

  ε-contraction-l :
    {g h k : Grammar} →
    ε-grammar ⊢ g →
    g ⊗ h ⊢ k →
    h ⊢ k
  ε-contraction-l {g = g} {k = k} e e' p =
    e' ((([] , _) , refl) , (e refl , p))

  ε-contraction-r :
    {g h k : Grammar} →
    ε-grammar ⊢ g →
    h ⊗ g ⊢ k →
    h ⊢ k
  ε-contraction-r {g = g} {k = k} e e' p =
    e' (((_ , []) , sym (++-unit-r _)) , (p , e refl))

  ⊗-intro :
    {g h k l : Grammar} →
    g ⊢ h →
    k ⊢ l →
    g ⊗ k ⊢ h ⊗ l
  ⊗-intro e e' p =
    p .fst , (e (p .snd .fst)) , (e' (p .snd .snd))

  ⊗-elim :
    {g h k l : Grammar} →
    g ⊢ h ⊗ k →
    h ⊗ k ⊢ l →
    g ⊢ l
  ⊗-elim e e' p =
    let (s , ph , pk) = e p in
    e' (s , (ph , pk))


  -⊗-intro :
    {g h k : Grammar} →
    g ⊗ h ⊢ k →
    h ⊢ g -⊗ k
  -⊗-intro e p w' q =
    e ((_ , refl) , (q , p))

  -⊗-elim :
    {g h k l : Grammar} →
    h ⊢ g -⊗ k →
    l ⊢ g →
    l ⊗ h ⊢ k
  -⊗-elim {k = k} e e' p =
    transport (sym (cong k (p .fst .snd)))
      (e (p .snd .snd) (fst p .fst .fst) (e' (p .snd .fst)))

  ⊗--intro :
    {g h k : Grammar} →
    g ⊗ h ⊢  k →
    g ⊢ k ⊗- h
  ⊗--intro e p w' q =
    e ((_ , refl) , p , q)

  ⊗--elim :
    {g h k l : Grammar} →
    g ⊢ k ⊗- h →
    l ⊢ h →
    g ⊗ l ⊢ k
  ⊗--elim {k = k} e e' p =
    transport
      (sym (cong k (p .fst .snd)))
      (e (p .snd .fst) (fst p .fst .snd) (e' (p .snd .snd)))

  ⊗-assoc :
    {g h k l : Grammar} →
    g ⊗ h ⊗ k ⊢  l →
    (g ⊗ h) ⊗ k ⊢ l
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
    (g ⊗ h) ⊗ k ⊢ l →
    g ⊗ h ⊗ k ⊢ l
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
    (∀ a → g ⊢ f a) →
    g ⊢ (LinearΠ f)
  LinearΠ-intro e p a = e a p

  LinearΠ-elim :
    {A : Type ℓ} → {f : A → Grammar} →
    {g : Grammar} →
    g ⊢ LinearΠ f →
    (a : A) →
    g ⊢ f a
  LinearΠ-elim e a p = e p a

  LinearΣ-intro :
    {A : Type ℓ} → {f : A → Grammar} →
    {g : Grammar} →
    (a : A) →
    g ⊢ f a →
    g ⊢ LinearΣ f
  LinearΣ-intro a e p = a , (e p)

  LinearΣ-elim :
    {A : Type ℓ} → {f : A → Grammar} →
    {g h : Grammar} →
    g ⊢ LinearΣ f →
    (∀ a → f a ⊢ h) →
    g ⊢ h
  LinearΣ-elim e e' p =
    let (a , b) = e p in
    e' a b

  ⊤-intro :
    {g : Grammar} →
    g ⊢ ⊤-grammar
  ⊤-intro p = tt*

  ⊥-elim :
    {g : Grammar} →
    ⊥-grammar ⊢ g
  ⊥-elim x = ⊥.elim (lower x)

  &-intro :
    {g h k : Grammar} →
    g ⊢ h →
    g ⊢ k →
    g ⊢ h & k
  &-intro e e' p =
    e p , e' p

  &-elim₁ :
    {g h k : Grammar} →
    g ⊢ h & k →
    g ⊢ h
  &-elim₁ e p = e p .fst

  &-elim₂ :
    {g h k : Grammar} →
    g ⊢ h & k →
    g ⊢ k
  &-elim₂ e p = e p .snd

  ⊕-intro₁ :
    {g h k : Grammar} →
    g ⊢ h →
    g ⊢ h ⊕ k
  ⊕-intro₁ e p = inl (e p)

  ⊕-intro₂ :
    {g h k : Grammar} →
    g ⊢ k →
    g ⊢ h ⊕ k
  ⊕-intro₂ e p = inr (e p)

  ⊕-elim :
    {g h k : Grammar} →
    g ⊢ k →
    h ⊢ k →
    g ⊕ h ⊢ k
  ⊕-elim eg eh p =
    Sum.elim
      (λ pg → eg pg)
      (λ ph → eh ph)
      p

  MaybeGrammar-yes-intro :
    {g h : Grammar} →
    g ⊢ h →
    g ⊢ MaybeGrammar h
  MaybeGrammar-yes-intro {g}{h} p = ⊕-intro₁ {g = g} {h = h} {k = ⊤-grammar} p

  MaybeGrammar-no-intro :
    {g h : Grammar} →
    g ⊢ MaybeGrammar h
  MaybeGrammar-no-intro {g}{h} = ⊕-intro₂ {g = g} {h = h} {k = ⊤-grammar} (⊤-intro {g = g})

  MaybeGrammar-elim :
    {g h : Grammar} →
    g ⊢ h →
    ⊤-grammar ⊢ h →
    MaybeGrammar g ⊢ h
  MaybeGrammar-elim = ⊕-elim

  MaybeGrammar-return :
    {g h : Grammar} →
    g ⊢ h →
    g ⊢ (MaybeGrammar h)
  MaybeGrammar-return = MaybeGrammar-yes-intro

  MaybeGrammar-bind :
    {g h : Grammar} →
    g ⊢ MaybeGrammar h →
    MaybeGrammar g ⊢ MaybeGrammar h
  MaybeGrammar-bind {g} {h} p =
    MaybeGrammar-elim {g = g} {h = MaybeGrammar h} p (MaybeGrammar-no-intro {g = ⊤-grammar} {h = h})


  DecProp-grammar'-intro :
    (d : DecProp ℓ) →
    {g : Grammar} →
    g ⊢ DecProp-grammar' d ⊕ DecProp-grammar' (negateDecProp d)
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
    g ⊢ h →
    ε-grammar ⊢ g ⇒ h
  ⇒-intro e pε pg = e pg

  -- TODO what should the implication elim be?
  -- ⇒-elim : {!!}
  -- ⇒-elim = {!!}

  KL*-elim :
    {g h : Grammar} →
    ε-grammar ⊢ h →
    g ⊗ h ⊢ h →
    KL* g ⊢ h
  KL*-elim pε p⊗ (nil x) = pε x
  KL*-elim {g}{h} pε p⊗ (cons x) =
    p⊗ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ (x .snd .snd))))

  foldKL*r = KL*-elim

  foldKL*l :
    {g h : Grammar } →
    ε-grammar ⊢ h →
    h ⊗ g ⊢ h →
    KL* g ⊢ h
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
    g ⊢ ∥ g ∥grammar
  ∥∥grammar-intro {g} p = ∣ p ∣₁

  ∥∥grammar-elim :
    {g h : Grammar} →
    isPropValuedGrammar h →
    g ⊢ h →
    ∥ g ∥grammar ⊢ h
  ∥∥grammar-elim isProph e p =
    Cubical.HITs.PropositionalTruncation.elim
    (λ _ → isProph)
    (λ pg → e pg)
    p

  trans :
    {g h k : Grammar} →
    g ⊢ h →
    h ⊢ k →
    g ⊢ k
  trans e e' p = e' (e p)

  ⊗-trans-l :
    {g h k l : Grammar} →
    g ⊢ h  →
    h ⊗ k ⊢ l →
    g ⊗ k ⊢ l
  ⊗-trans-l {g}{h}{k}{l} e e' =
    ⊗--elim {g = g} {h = k} {k = l} {l = k}
      (trans {g = g} {h = h} {k = l ⊗- k}
        e
        (⊗--intro {g = h} {h = k} {k = l} e')
      )
      (id {g = k})

  ⊗-trans-r :
    {g h k l : Grammar} →
    g ⊢ h  →
    k ⊗ h ⊢ l →
    k ⊗ g ⊢ l
  ⊗-trans-r {g}{h}{k}{l} e e' =
    -⊗-elim {g = k} {h = g} {k = l} {l = k}
      (trans {g = g} {h = h} {k = k -⊗ l}
        e
        (-⊗-intro {g = k} {h = h} {k = l} e'))
      (id {g = k})

  -- The following type allows to induct over well-behaved contexts to build a
  -- powerful cut principle
  -- We wish to define something like:
  --   cut :
  --      {g h k : Grammar} →
  --      (Δ : Grammar → Grammar) →
  --      g ⊢ h →
  --      Δ h ⊢ k →
  --      Δ g ⊢ k
  --  However this isn't possible for arbitrary functions Δ
  --  but we can define terms like this for nice enough Δ
  --  (i.e. contexts that have a single free variable)
  --
  -- This isn't meant to be used everywhere, however this can eliminate redundancy in a lot of proofs
  -- because without use of it, we must manually conjugate with the introudction and elimination forms
  -- like in ⊗-trans-l below, which can become arbitrarily long
  --
  -- Instead below we do this work once. And for brevity, we are doing it "in assembly" so to speak.
  -- i.e. for this first pass, we are breaking abstractions to avoid the conjugations of intro/elim, but
  -- the result is equivalent in either case
  data OneHoleContext : Type (ℓ-suc ℓ) where
    var : OneHoleContext
    ⊗l : Grammar → OneHoleContext
    ⊗r : Grammar → OneHoleContext
    ⊕l : Grammar → OneHoleContext
    ⊕r : Grammar → OneHoleContext
    -- -⊗l : Grammar → OneHoleContext
    -⊗r : Grammar → OneHoleContext
    ⊗-l : Grammar → OneHoleContext
    -- ⊗-r : Grammar → OneHoleContext
    includeGrammar : Grammar → OneHoleContext
    _⊗OH_ : OneHoleContext  → OneHoleContext  → OneHoleContext
    _⊕OH_ : OneHoleContext  → OneHoleContext  → OneHoleContext
    _-⊗OH_ : Grammar  → OneHoleContext  → OneHoleContext
    _⊗-OH_ : OneHoleContext  → Grammar  → OneHoleContext

  syntax ⊗l g = hole ⊗ g
  syntax ⊗r g = g ⊗ hole
  syntax ⊕l g = g ⊕ hole
  syntax ⊕r g = hole ⊕ g
  syntax -⊗r g = g -⊗ hole
  syntax ⊗-l g = hole ⊗- g
  syntax includeGrammar g = ↑ g

  evalOHContext : OneHoleContext → Grammar → Grammar
  evalOHContext var g = g
  evalOHContext (⊗l x) g = g ⊗ x
  evalOHContext (⊗r x) g = x ⊗ g
  evalOHContext (⊕l x) g = g ⊕ x
  evalOHContext (⊕r x) g = x ⊕ g
  -- only allow the positive occurences of g
  -- evalOHContext (-⊗l x) g = g -⊗ x
  evalOHContext (-⊗r x) g = x -⊗ g
  evalOHContext (⊗-l x) g = g ⊗- x
  -- evalOHContext (⊗-r x) g = x ⊗- g
  evalOHContext (includeGrammar x) g = x
  evalOHContext (x ⊗OH y) g = (evalOHContext x g) ⊗ (evalOHContext y g)
  evalOHContext (x ⊕OH y) g = (evalOHContext x g) ⊕ (evalOHContext y g)
  evalOHContext (h -⊗OH y) g = h -⊗ (evalOHContext y g)
  evalOHContext (x ⊗-OH h) g = (evalOHContext x g) ⊗- h

  syntax evalOHContext Δ g = Δ [ g ]eval

  cut :
    {g h k : Grammar} →
    (Δ : OneHoleContext) →
    g ⊢ h →
    Δ [ h ]eval ⊢ k →
    Δ [ g ]eval ⊢ k
  cut {g} {h} {k} var g⊢h Δh⊢k = trans {g = g} {h = h} {k = k} g⊢h Δh⊢k
  cut {g} {h} {k} (⊗l x) g⊢h Δh⊢k (s , pg , px) = Δh⊢k (s , ((g⊢h pg) , px))
  cut {g} {h} {k} (⊗r x) g⊢h Δh⊢k (s , px , pg) = Δh⊢k (s , (px , g⊢h pg))
  cut {g} {h} {k} (⊕l x) g⊢h Δh⊢k (inl pg) = Δh⊢k (inl (g⊢h pg))
  cut {g} {h} {k} (⊕l x) g⊢h Δh⊢k (inr px) = Δh⊢k (inr px)
  cut {g} {h} {k} (⊕r x) g⊢h Δh⊢k (inr pg) = Δh⊢k (inr (g⊢h pg))
  cut {g} {h} {k} (⊕r x) g⊢h Δh⊢k (inl px) = Δh⊢k (inl px)
  -- cut {g} {h} {k} (-⊗l x) g⊢h Δh⊢k p = {!!}
  cut {g} {h} {k} (-⊗r x) g⊢h Δh⊢k p = Δh⊢k (λ w' px → g⊢h (p w' px))
  cut {g} {h} {k} (⊗-l x) g⊢h Δh⊢k p = Δh⊢k (λ w' px → g⊢h (p w' px))
  -- cut {g} {h} {k} (⊗-r x) g⊢h Δh⊢k p = {!!}
  cut {g} {h} {k} (includeGrammar x) g⊢h Δh⊢k p = Δh⊢k p
  cut {g} {h} {k} (Δ ⊗OH Δ₁) g⊢h Δh⊢k (s , p , p') =
    Δh⊢k (s , (cut {g}{h}{Δ [ h ]eval} Δ g⊢h (id {g = Δ [ h ]eval}) p) ,
              (cut {g}{h}{Δ₁ [ h ]eval} Δ₁ g⊢h (id {g = Δ₁ [ h ]eval}) p'))
  cut {g} {h} {k} (Δ ⊕OH Δ₁) g⊢h Δh⊢k (inl p) =
    Δh⊢k (inl (cut {g}{h}{Δ [ h ]eval} Δ g⊢h (id {g = Δ [ h ]eval}) p))
  cut {g} {h} {k} (Δ ⊕OH Δ₁) g⊢h Δh⊢k (inr p) =
    Δh⊢k (inr (cut {g}{h}{Δ₁ [ h ]eval} Δ₁ g⊢h (id {g = Δ₁ [ h ]eval}) p))
  cut {g} {h} {k} (l -⊗OH Δ) g⊢h Δh⊢k p =
    Δh⊢k (λ w' pl → cut {g}{h}{Δ [ h ]eval} Δ g⊢h (id {g = Δ [ h ]eval}) (p w' pl))
  cut {g} {h} {k} (Δ ⊗-OH l) g⊢h Δh⊢k p =
    Δh⊢k (λ w' pl → cut {g}{h}{Δ [ h ]eval} Δ g⊢h (id {g = Δ [ h ]eval}) (p w' pl))

  ⊗-trans-l' :
    {g h k l : Grammar} →
    g ⊢ h  →
    h ⊗ k ⊢ l →
    g ⊗ k ⊢ l
  ⊗-trans-l' {g}{h}{k}{l} e e' =
    cut {g = g} {h = h} {k = l} (hole ⊗ k) e e'

  trans' :
    {g h k : Grammar} →
    g ⊢ h →
    h ⊢ k →
    g ⊢ k
  trans' {g}{h}{k} e e' = cut {g = g} {h = h} {k = k} var e e'

  cut-test :
    {g h j k l m n o p q : Grammar} →
    g ⊢ h →
    j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h)))) ⊢ q →
    j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g)))) ⊢ q
  cut-test {g}{h}{j}{k}{l}{m}{n}{o}{p}{q} e e' =
    cut {g = g} {h = h} {k = q}
      (j -⊗OH (k -⊗OH ((↑ l) ⊗OH ((↑ m) ⊕OH (p -⊗ hole)))))
      e e'
