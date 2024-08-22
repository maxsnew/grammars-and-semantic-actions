open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels

module Semantics.Term.Rules ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

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

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

id : g ⊢ g
id x = x

seq :
  g ⊢ h →
  h ⊢ k →
  g ⊢ k
seq e e' p = e' (e p)

⊗-intro :
  g ⊢ h →
  k ⊢ l →
  g ⊗ k ⊢ h ⊗ l
⊗-intro e e' p =
  p .fst , (e (p .snd .fst)) , (e' (p .snd .snd))

⊗-unit-r :
  g ⊗ ε-grammar ⊢ g
⊗-unit-r {g = g} p =
  transport
    (cong g
      (sym (++-unit-r (fst p .fst .fst)) ∙
      cong (p .fst .fst .fst ++_) (sym (p .snd .snd)) ∙
      sym (p .fst .snd)))
    (p .snd .fst)

⊗-unit-r⁻ :
  g ⊢ g ⊗ ε-grammar
⊗-unit-r⁻ p =
  ((_ , []) , (sym (++-unit-r _))) , (p , refl)

⊗-unit-l :
  ε-grammar ⊗ g ⊢ g
⊗-unit-l {g = g} p =
  transport
    (cong g (cong (_++  p .fst .fst .snd)
      (sym (p .snd .fst)) ∙ sym (p .fst .snd)))
    (p .snd .snd)

⊗-unit-l⁻ :
  g ⊢ ε-grammar ⊗ g
⊗-unit-l⁻ p =
  (([] , _) , refl) , (refl , p)

⊗-assoc :
  g ⊗ (h ⊗ k) ⊢ (g ⊗ h) ⊗ k
⊗-assoc p =
  ((fst p .fst .fst ++ fst (p .snd .snd) .fst .fst , fst (p .snd .snd) .fst .snd) ,
    p .fst .snd ∙
    cong (p .fst .fst .fst ++_) (p .snd .snd .fst .snd) ∙
    sym
    (++-assoc
      (p .fst .fst .fst)
      (p .snd .snd .fst .fst .fst)
      (p .snd .snd .fst .fst .snd))) ,
  ((((fst p .fst .fst , fst (p .snd .snd) .fst .fst) ,
    refl) ,
  ((p .snd .fst) , (p .snd .snd .snd .fst))) , (p .snd .snd .snd .snd))

⊗-assoc⁻ :
  (g ⊗ h) ⊗ k ⊢ g ⊗ (h ⊗ k)
⊗-assoc⁻ p =
  (((fst (p .snd .fst) .fst .fst) , (fst (p .snd .fst) .fst .snd ++ fst p .fst .snd)) ,
    (p .fst .snd ∙
    cong (_++ p .fst .fst .snd) (p .snd .fst .fst .snd) ∙
    ++-assoc
      (p .snd .fst .fst .fst .fst)
      (p .snd .fst .fst .fst .snd)
      (p .fst .fst .snd))) ,
    (p .snd .fst .snd .fst ,
    (((fst (p .snd .fst) .fst .snd , fst p .fst .snd) ,
      refl) ,
    (p .snd .fst .snd .snd ,
    p .snd .snd)))

-⊗-intro :
  g ⊗ h ⊢ k →
  h ⊢ g -⊗ k
-⊗-intro e p w' q =
  e ((_ , refl) , (q , p))

-⊗-app :
  g ⊗ (g -⊗ h) ⊢ h
-⊗-app {h = h} p = subst h (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

-⊗-intro⁻ :
  g ⊢ h -⊗ k →
  h ⊗ g ⊢ k
-⊗-intro⁻ {h = h}{k = k} f =
  seq {h = h ⊗ (h -⊗ k)}
    (⊗-intro (id {g = h}) f)
    -⊗-app

-⊗-β :
  ∀ (m : (g ⊗ h) ⊢ k) →
  Path ((g ⊗ h) ⊢ k)
    (-⊗-intro⁻ {g = h}{h = g}{k = k} (-⊗-intro {g = g}{h = h}{k = k} m))
    m
-⊗-β {k = k} m = implicitFunExt (funExt (λ p⊗ →
  fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
    (congP (λ _ → m) (⊗PathP refl refl))))

-⊗-η : ∀ (f : g ⊢ h -⊗ k)
  → Path (g ⊢ h -⊗ k)
      f
      (-⊗-intro {g = h}{h = g}{k = k} (-⊗-intro⁻ {g = g}{h = h}{k = k} f))
-⊗-η f = implicitFunExt (funExt (λ p⊗ →
  funExt (λ w' → funExt λ q⊗ → sym (transportRefl (f p⊗ w' q⊗)) )))

⊗--intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⊗- h
⊗--intro e p w' q =
  e ((_ , refl) , p , q)

⊗--app :
  (g ⊗- h) ⊗ h ⊢ g
⊗--app {g = g} p =
  transport
    (cong g (sym (p .fst .snd)))
    (p .snd .fst (fst p .fst .snd) (p .snd .snd))

⊗--intro⁻ :
  g ⊢ h ⊗- k →
  g ⊗ k ⊢ h
⊗--intro⁻ {h = h}{k = k} f =
  seq {h = (h ⊗- k) ⊗ k}
    (⊗-intro f (id {g = k}))
    ⊗--app

⊗--β :
  ∀ (m : g ⊗ h ⊢ k) →
  Path (g ⊗ h ⊢ k)
    (⊗--intro⁻ {g = g}{h = k}{k = h} (⊗--intro {g = g}{h = h}{k = k} m))
    m
⊗--β {k = k} m =
  implicitFunExt (funExt (λ p⊗ →
    fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
      (congP (λ _ → m) (⊗PathP refl refl))))

⊗--η : ∀ (f : g ⊢ h ⊗- k)
  → Path (g ⊢ h ⊗- k)
      f
      (⊗--intro {g = g}{h = k}{k = h} (⊗--intro⁻ {g = g}{h = h}{k = k} f))
⊗--η f =
  implicitFunExt (funExt (λ p⊗ →
    funExt (λ w' → funExt λ q⊗ → sym (transportRefl (f p⊗ w' q⊗)))))

⊤-intro :
  g ⊢ ⊤-grammar {ℓG = ℓ}
⊤-intro p = tt*

⊥-elim :
  ⊥-grammar {ℓG = ℓ} ⊢ g
⊥-elim x = ⊥.elim (lower x)

&-intro :
  g ⊢ h →
  g ⊢ k →
  g ⊢ h & k
&-intro e e' p =
  e p , e' p

&-π₁ :
  g & h ⊢ g
&-π₁ p = p .fst

&-π₂ :
  g & h ⊢ h
&-π₂ p = p .snd

&-β₁ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  Path (g ⊢ h)
    (seq {h = h & k} (&-intro {g = g}{h = h}{k = k} e₁ e₂) (&-π₁ {g = h}{h = k}))
    e₁
&-β₁ e₁ e₂ = refl

&-β₂ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  Path (g ⊢ k)
    (seq {h = h & k} (&-intro {g = g}{h = h}{k = k} e₁ e₂) (&-π₂ {g = h}{h = k}))
    e₂
&-β₂ e₁ e₂ = refl

&-η :
  (e : g ⊢ h & k) →
  Path (g ⊢ h & k)
    (&-intro {g = g}{h = h}{k = k}
      (seq {h = h & k} e (&-π₁ {g = h}{h = k}))
      (seq {h = h & k} e (&-π₂ {g = h}{h = k})))
    e
&-η e = refl

⊕-inl :
  g ⊢ g ⊕ h
⊕-inl p = inl p

⊕-inr :
  g ⊢ h ⊕ g
⊕-inr p = inr p

⊕-elim :
  g ⊢ h →
  k ⊢ h →
  g ⊕ k ⊢ h
⊕-elim eg eh p =
  Sum.elim
    (λ pg → eg pg)
    (λ ph → eh ph)
    p

⊕-βl :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  Path (g ⊢ g ⊕ h)
    (seq {h = g ⊕ h} (⊕-inl {g = g}{h = h}) (⊕-elim {g = g}{h = g ⊕ h}{k = h} e₁ e₂))
    e₁
⊕-βl e₁ e₂ = refl

⊕-βr :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  Path (h ⊢ g ⊕ h)
    (seq {h = g ⊕ h} (⊕-inr {g = h}{h = g}) (⊕-elim {g = g}{h = g ⊕ h}{k = h} e₁ e₂))
    e₂
⊕-βr e₁ e₂ = refl

⊕-η :
  (e : g ⊕ h ⊢ k) →
  Path (g ⊕ h ⊢ k)
    (⊕-elim {g = g}{h = k}{k = h}
      (seq {h = g ⊕ h} (⊕-inl {g = g}{h = h}) e)
      (seq {h = g ⊕ h} (⊕-inr {g = h}{h = g}) e))
    e
⊕-η e i (inl x) = e (inl x)
⊕-η e i (inr x) = e (inr x)

⇒-intro :
  g & h ⊢ k →
  g ⊢ h ⇒ k
⇒-intro e pg = λ ph → e (pg , ph)

⇒-app :
  g & (g ⇒ h) ⊢ h
⇒-app (pg , f) = f pg

KL*-elim :
  ε-grammar ⊢ g →
  h ⊗ g ⊢ g →
  KL* h ⊢ g
KL*-elim pε p⊗ (nil x) = pε x
KL*-elim {g}{h} pε p⊗ (cons x) =
  p⊗ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ (x .snd .snd))))

foldKL*r = KL*-elim

foldKL*l :
  ε-grammar ⊢ g →
  g ⊗ h ⊢ g →
  KL* h ⊢ g
foldKL*l {g = g}{h = h} pε p⊗ =
  seq {g = KL* h}{h = g -⊗ g}{k = g}
    (foldKL*r {g = g -⊗ g}{h = h}
      (-⊗-intro {g = g}{h = ε-grammar}{k = g} ⊗-unit-r)
      (-⊗-intro {g = g}{h = h ⊗ (g -⊗ g)}{k = g}
        (seq {h = (g ⊗ h) ⊗ (g -⊗ g)}
          (⊗-assoc {g = g}{h = h}{k = g -⊗ g})
          (seq {h = g ⊗ (g -⊗ g)}
            (⊗-intro {g = g ⊗ h}{h = g}{k = g -⊗ g}{l = g -⊗ g} p⊗ (id {g = g -⊗ g}))
            -⊗-app))))
    (seq {g = g -⊗ g}{h = g ⊗ (g -⊗ g)}{k = g}
      (seq {h = ε-grammar ⊗ (g -⊗ g)}
        (⊗-unit-l⁻ {g = g -⊗ g})
        (⊗-intro {g = ε-grammar}{h = g}{k = g -⊗ g}{l = g -⊗ g} pε (id {g = g -⊗ g})))
      -⊗-app)

-- These linear dependent terms should probably not be used.
-- It's preferable to have them be managed at the
-- boundary between the embedded language and Agda
LinearΠ-intro :
  {A : Type ℓ} → {f : A → Grammar ℓ} →
  (∀ a → g ⊢ f a) →
  g ⊢ (LinearΠ f)
LinearΠ-intro e p a = e a p

LinearΠ-elim :
  {A : Type ℓ} → {f : A → Grammar ℓ} →
  g ⊢ LinearΠ f →
  (a : A) →
  g ⊢ f a
LinearΠ-elim e a p = e p a

LinearΣ-intro :
  {A : Type ℓ} → {f : A → Grammar ℓ} →
  (a : A) →
  g ⊢ f a →
  g ⊢ LinearΣ f
LinearΣ-intro a e p = a , (e p)

LinearΣ-elim :
  {A : Type ℓ} → {f : A → Grammar ℓ} →
  g ⊢ LinearΣ f →
  (∀ a → f a ⊢ h) →
  g ⊢ h
LinearΣ-elim e e' p =
  let (a , b) = e p in
  e' a b


-- DecProp-grammar'-intro :
--   ∀ {ℓ ℓg : Level} →
--   (d : DecProp ℓ) →
--   {g : Grammar ℓg} →
--   g ⊢ DecProp-grammar' {ℓG = ℓg} d ⊕ DecProp-grammar' {ℓG = ℓg}(negateDecProp d)
-- DecProp-grammar'-intro {ℓ}{ℓg = ℓg}(a , yes x) {g} p =
--   ⊕-intro₁
--     {g = g}
--     {h = DecProp-grammar' {ℓG = ℓg}((a , yes x))}
--     {k = DecProp-grammar' {ℓG = ℓg}(negateDecProp (a , yes x))}
--     (⊤-intro {g = g})
--     p
-- DecProp-grammar'-intro {ℓ}{ℓg = ℓg}(a , no ¬x) {g} p =
--   ⊕-intro₂
--     {g = g}
--     {h = DecProp-grammar' {ℓG = ℓg} (negateDecProp (a , no ¬x))}
--     {k = DecProp-grammar' {ℓG = ℓg} ((a , no ¬x))}
--     (⊤-intro {g = g})
--     p


-- LowerGrammarTerm :
--   ∀ {ℓ} →
--   {g : Grammar ℓg} →
--   LiftGrammar {ℓG = ℓg}{ℓ} g ⊢ g
-- LowerGrammarTerm {ℓ = ℓ} {g = g} x = lower x

-- LiftGrammarTerm :
--   ∀ {ℓ} →
--   {g : Grammar ℓg} →
--   g ⊢ LiftGrammar {ℓG = ℓg}{ℓ} g
-- LiftGrammarTerm {ℓ = ℓ} {g = g} x = lift x

-- -- curry⊗- :
-- --   {g : Grammar {Σ₀} ℓg} →
-- --   {h : Grammar {Σ₀} ℓh} →
-- --   {k : Grammar {Σ₀} ℓk} →
-- --   g ⊗- (h ⊗- k) ⊢ (g ⊗- h) ⊗- k
-- -- curry⊗- {g = g}{h = h}{k = k} =
-- --   ⊗--intro {g = g ⊗- (h ⊗- k)} {h = k} {k = g ⊗- h}
-- --     {!!}
-- --   --   (⊗--intro {g = (g ⊗- (h ⊗- k)) ⊗ k} {h = h} {k = g}
-- --   --     (⊗-assoc {g = g ⊗- (h ⊗- k)} {h = k} {k = h} {l = g}
-- --   --       {!functoriality {g = k ⊗ h} {h = h ⊗- k}!}))
