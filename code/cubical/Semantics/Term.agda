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

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' ℓΣ₀ : Level
    Σ₀ : Type ℓΣ₀
    g : Grammar ℓg {Σ₀}
    h : Grammar ℓh {Σ₀}
    k : Grammar ℓk {Σ₀}
    l : Grammar ℓl {Σ₀}

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
 --
id : g ⊢ g
id x = x

ε-extension-r :
  g ⊢ ε-grammar {ℓG = ℓ} →
  h ⊢ k →
  h ⊗ g ⊢ k
ε-extension-r {g = g} {k = k} e e' p =
  transport
    (cong k ((sym (++-unit-r (fst p .fst .fst)) ∙
    cong (λ a → p .fst .fst .fst ++ a) (sym (lower (e (p .snd .snd))))) ∙
    sym (p .fst .snd)))
    (e' (p .snd .fst))

ε-extension-l :
  g ⊢ ε-grammar {ℓG = ℓ}  →
  h ⊢ k →
  g ⊗ h ⊢ k
ε-extension-l {g = g} {k = k} e e' p =
  transport
    (cong k (cong (λ a → a ++ p .fst .fst .snd) (sym (lower (e (p .snd .fst)))) ∙
      sym (p .fst .snd)))
    (e' (p .snd .snd))

ε-contraction-l :
  ε-grammar {ℓG = ℓ} ⊢ g →
  g ⊗ h ⊢ k →
  h ⊢ k
ε-contraction-l {g = g} {k = k} e e' p =
  e' ((([] , _) , refl) , (e (lift refl) , p))

ε-contraction-r :
  ε-grammar {ℓG = ℓ} ⊢ g →
  h ⊗ g ⊢ k →
  h ⊢ k
ε-contraction-r {g = g} {k = k} e e' p =
  e' (((_ , []) , sym (++-unit-r _)) , (p , e (lift refl)))

ε-on-right :
  g ⊢ g ⊗ ε-grammar {ℓG = ℓ}
ε-on-right {w = w} p =
  ((w , []) , sym (++-unit-r w)) , p , (lift refl)

ε-on-left :
  g ⊢ ε-grammar {ℓG = ℓ} ⊗ g
ε-on-left {w = w} p =
  (([] , w) , refl) , (lift refl) , p

⊗-intro :
  g ⊢ h →
  k ⊢ l →
  g ⊗ k ⊢ h ⊗ l
⊗-intro e e' p =
  p .fst , (e (p .snd .fst)) , (e' (p .snd .snd))

syntax ⊗-intro e e' = [ e , e' ]

⊗-elim :
  g ⊢ h ⊗ k →
  h ⊗ k ⊢ l →
  g ⊢ l
⊗-elim e e' p =
  let (s , ph , pk) = e p in
  e' (s , (ph , pk))

syntax ⊗-elim {h = h}{k = k} e e' = let[ h , k ]=[ e ]in[ e' ]

-⊗-intro :
  g ⊗ h ⊢ k →
  h ⊢ g -⊗ k
-⊗-intro e p w' q =
  e ((_ , refl) , (q , p))

syntax -⊗-intro {g = g} e = λ-⊗[ x ∈ g ][ e ]

-⊗-elim :
  g ⊢ h -⊗ k →
  l ⊢ h →
  l ⊗ g ⊢ k
-⊗-elim {k = k} e e' p =
  transport (sym (cong k (p .fst .snd)))
    (e (p .snd .snd) (fst p .fst .fst) (e' (p .snd .fst)))

syntax -⊗-elim {h = h}{k = k} e e' = e' -⊗app[ h -⊗ k ] e

⊗--intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⊗- h
⊗--intro e p w' q =
  e ((_ , refl) , p , q)

⊗--elim :
  g ⊢ h ⊗- k →
  l ⊢ k →
  g ⊗ l ⊢ h
⊗--elim {h = h} e e' p =
  transport
    (sym (cong h (p .fst .snd)))
    (e (p .snd .fst) (fst p .fst .snd) (e' (p .snd .snd)))

⊗-assoc :
  g ⊗ h ⊗ k ⊢ l →
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
  {A : Type ℓ} → {f : A → Grammar ℓ'} →
  (∀ a → g ⊢ f a) →
  g ⊢ (LinearΠ f)
LinearΠ-intro e p a = e a p

LinearΠ-elim :
  {A : Type ℓ} → {f : A → Grammar ℓ'} →
  g ⊢ LinearΠ f →
  (a : A) →
  g ⊢ f a
LinearΠ-elim e a p = e p a

LinearΣ-intro :
  {A : Type ℓ} → {f : A → Grammar ℓ'} →
  (a : A) →
  g ⊢ f a →
  g ⊢ LinearΣ f
LinearΣ-intro a e p = a , (e p)

LinearΣ-elim :
  {A : Type ℓ} → {f : A → Grammar ℓ'} →
  g ⊢ LinearΣ f →
  (∀ a → f a ⊢ h) →
  g ⊢ h
LinearΣ-elim e e' p =
  let (a , b) = e p in
  e' a b

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

&-elim₁ :
  g ⊢ h & k →
  g ⊢ h
&-elim₁ e p = e p .fst

&-elim₂ :
  g ⊢ h & k →
  g ⊢ k
&-elim₂ e p = e p .snd

⊕-intro₁ :
  g ⊢ h →
  g ⊢ h ⊕ k
⊕-intro₁ e p = inl (e p)

⊕-intro₂ :
  g ⊢ h →
  g ⊢ k ⊕ h
⊕-intro₂ e p = inr (e p)

⊕-elim :
  g ⊢ h →
  k ⊢ h →
  g ⊕ k ⊢ h
⊕-elim eg eh p =
  Sum.elim
    (λ pg → eg pg)
    (λ ph → eh ph)
    p

trans :
  g ⊢ h →
  h ⊢ k →
  g ⊢ k
trans e e' p = e' (e p)

⊗-trans-l :
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh {Σ₀}} →
  {k : Grammar ℓk {Σ₀}} →
  {l : Grammar ℓl {Σ₀}} →
  g ⊢ h  →
  h ⊗ k ⊢ l →
  g ⊗ k ⊢ l
⊗-trans-l {g = g}{h = h}{k = k}{l = l} e e' =
  ⊗--elim {g = g} {h = l} {k = k} {l = k}
    (trans {g = g} {h = h} {k = l ⊗- k} e
      (⊗--intro {g = h} {h = k} {k = l} e'))
    (id {g = k})

⊗-trans-r :
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh {Σ₀}} →
  {k : Grammar ℓk {Σ₀}} →
  {l : Grammar ℓl {Σ₀}} →
  g ⊢ h  →
  k ⊗ h ⊢ l →
  k ⊗ g ⊢ l
⊗-trans-r {g = g}{h = h}{k = k}{l = l} e e' =
  -⊗-elim {g = g} {h = k} {k = l} {l = k}
    (trans {g = g} {h = h} {k = k -⊗ l}
      e
      (-⊗-intro {g = k} {h = h} {k = l} e'))
    (id {g = k})

-- The following type allows us to induct over well-behaved contexts to build a
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
--  (i.e. contexts that have a single free variable that occurs positively amongst a
--    restricted set of context constructors)
--
-- This isn't meant to be used everywhere, however this can eliminate redundancy in a lot of proofs
-- because without use of it, we must manually conjugate with the introudction and elimination forms
-- like in ⊗-trans-l below, which can become arbitrarily long
--
-- Instead below we do this work once. And for brevity, we are doing it "in assembly" so to speak.
-- i.e. are breaking abstractions
data OneHoleContext (Σ₀ : Type ℓΣ₀) : (L : Level) → Typeω where
  var : OneHoleContext Σ₀ ℓ-zero
  _⊗l_ : ∀ {L}{L'} → OneHoleContext Σ₀ L' → Grammar L {Σ₀} → OneHoleContext Σ₀ (ℓ-max (ℓ-max ℓΣ₀ L) L')
  _⊗r_ : ∀ {L}{L'} → Grammar L {Σ₀} → OneHoleContext Σ₀ L' → OneHoleContext Σ₀  (ℓ-max (ℓ-max ℓΣ₀ L) L')
  _⊕l_ : ∀ {L}{L'} → OneHoleContext Σ₀ L' → Grammar L {Σ₀} → OneHoleContext Σ₀ (ℓ-max L L')
  _⊕r_ : ∀ {L}{L'} → Grammar L {Σ₀} → OneHoleContext Σ₀ L' → OneHoleContext Σ₀ (ℓ-max L L')
  _⊗OH_ : ∀ {L} {L'} → OneHoleContext Σ₀ L → OneHoleContext Σ₀ L' → OneHoleContext Σ₀ (ℓ-max (ℓ-max L ℓΣ₀) L')
  _⊕OH_ : ∀ {L} {L'} → OneHoleContext Σ₀ L → OneHoleContext Σ₀ L' → OneHoleContext Σ₀ (ℓ-max L L')
  _-⊗OH_ : ∀ {L} {L'} → Grammar L {Σ₀}  → OneHoleContext Σ₀ L' → OneHoleContext Σ₀ (ℓ-max (ℓ-max L ℓΣ₀) L')
  _⊗-OH_ : ∀ {L} {L'} → OneHoleContext Σ₀ L  → Grammar L' {Σ₀} → OneHoleContext Σ₀ (ℓ-max (ℓ-max L ℓΣ₀) L')

evalOHContext : ∀ {Σ₀} {L} {L'} → OneHoleContext {ℓΣ₀} Σ₀ L → Grammar L' {Σ₀} → Grammar (ℓ-max L L') {Σ₀}
evalOHContext var g = g
evalOHContext (x ⊗l h) g = (evalOHContext x g) ⊗ h
evalOHContext (h ⊗r x) g = h ⊗ evalOHContext x g
evalOHContext (x ⊕l h) g = (evalOHContext x g) ⊕ h
evalOHContext (h ⊕r x) g = h ⊕ evalOHContext x g
evalOHContext (x ⊗OH y) g = (evalOHContext x g) ⊗ (evalOHContext y g)
evalOHContext (x ⊕OH y) g = (evalOHContext x g) ⊕ (evalOHContext y g)
evalOHContext (h -⊗OH x) g = h -⊗ (evalOHContext x g)
evalOHContext (x ⊗-OH h) g = (evalOHContext x g) ⊗- h

syntax evalOHContext Δ g = Δ [ g ]eval

cut :
  ∀ {ℓ} →
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh} →
  (Δ : OneHoleContext Σ₀ ℓ) →
  g ⊢ h →
  Δ [ g ]eval ⊢ Δ [ h ]eval
cut {g = g}{h = h} var g⊢h = g⊢h
cut {g = g}{h = h} (x ⊗l l) g⊢h =
  ⊗-trans-l {g = evalOHContext x g} {h = evalOHContext x h} {k = l} {l = evalOHContext x h ⊗ l}
  (cut {g = g}{h = h} x g⊢h)
   (id {g = evalOHContext x h ⊗ l})
cut {g = g}{h = h} (l ⊗r x) g⊢h =
  ⊗-trans-r {g = evalOHContext x g} {h = evalOHContext x h} {k = l} {l = l ⊗ evalOHContext x h }
  (cut {g = g}{h = h} x g⊢h)
   (id {g = l ⊗ evalOHContext x h})
cut {g = g}{h = h} (x ⊕l l) g⊢h =
  ⊕-elim {g = evalOHContext x g} {h = evalOHContext x h ⊕ l}
   (⊕-intro₁ {g = evalOHContext x g} {h = evalOHContext x h} {k = l}
     (cut {g = g}{h = h} x g⊢h))
   (⊕-intro₂ {g = l} {h = l} {k = evalOHContext x h} (id {g = l}))
cut {g = g}{h = h} (l ⊕r x) g⊢h =
  ⊕-elim {g = l} {h = l ⊕ evalOHContext x h}
   (⊕-intro₁ {g = l} {h = l} {k = evalOHContext x h} (id {g = l}))
   (⊕-intro₂ {g = evalOHContext x g} {h = evalOHContext x h} {k = l}
     (cut {g = g}{h = h} x g⊢h))
cut {g = g}{h = h} (x ⊗OH y) g⊢h =
   (⊗-intro {g = evalOHContext x g} {h = evalOHContext x h}
     {k = evalOHContext y g} {l = evalOHContext y h}
     (cut {g = g} {h = h}  x g⊢h)
     (cut {g = g} {h = h}  y g⊢h)
     )
cut {g = g}{h = h} (x ⊕OH y) g⊢h =
   (⊕-elim {g = evalOHContext x g}
     {h = evalOHContext x h ⊕ evalOHContext y h} {k = evalOHContext y g}
     (⊕-intro₁ {g = evalOHContext x g} {h = evalOHContext x h}
       {k = evalOHContext y h} (cut {g = g}{h = h} x g⊢h )
     )
     (⊕-intro₂ {g = evalOHContext y g} {h = evalOHContext y h}
       {k = evalOHContext x h} (cut {g = g}{h = h} y g⊢h )
     )
     )
cut {g = g}{h = h} (l -⊗OH x) g⊢h =
   (-⊗-intro {g = l} {h = l -⊗ evalOHContext x g}
     {k = evalOHContext x h}
     (trans {g = l ⊗ (l -⊗ evalOHContext x g)} {h = evalOHContext x g}
       {k = evalOHContext x h}
       (-⊗-elim {g = l -⊗ evalOHContext x g} {h = l}
         {k = evalOHContext x g} {l = l}
           (id {g = l -⊗ evalOHContext x g}) (id {g = l}))
       (cut {g = g} {h = h} x g⊢h )))
cut {g = g}{h = h} (x ⊗-OH l) g⊢h =
   (⊗--intro {g = evalOHContext x g ⊗- l} {h = l}
     {k = evalOHContext x h}
     (trans {g = (evalOHContext x g ⊗- l) ⊗ l} {h = evalOHContext x g}
       {k = evalOHContext x h}
         (⊗--elim {g = evalOHContext x g ⊗- l} {h = evalOHContext x g}
           {k = l} {l = l}
             (id {g = evalOHContext x g ⊗- l})
             (id {g = l}))
         (cut {g = g}{h = h} x g⊢h )))

⊗-trans-l' :
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh {Σ₀}} →
  {k : Grammar ℓk {Σ₀}} →
  {l : Grammar ℓl {Σ₀}} →
  g ⊢ h  →
  h ⊗ k ⊢ l →
  g ⊗ k ⊢ l
⊗-trans-l' {g = g}{h = h}{k = k}{l = l} e e' =
  trans {g = g ⊗ k} {h = h ⊗ k} { k = l }
  (cut {g = g} {h = h} (var ⊗l k) e)
  e'

cut-test :
  {g h j k l m n o p q : Grammar ℓg {Σ₀}} →
  g ⊢ h →
  j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h)))) ⊢ q →
  j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g)))) ⊢ q
cut-test {g = g}{h}{j}{k}{l}{m}{n}{o}{p}{q} e e' =
  trans {g = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g))))}
   {h = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h))))} {k = q}
   (cut {g = g} {h = h}
     (j -⊗OH (k -⊗OH (l ⊗r (m ⊕r (p -⊗OH var)))))
     e)
   e'

DecProp-grammar'-intro :
  ∀ {ℓ ℓg : Level} →
  (d : DecProp ℓ) →
  {g : Grammar ℓg {Σ₀}} →
  g ⊢ DecProp-grammar' {ℓG = ℓg} d ⊕ DecProp-grammar' {ℓG = ℓg}(negateDecProp d)
DecProp-grammar'-intro {ℓ}{ℓg = ℓg}(a , yes x) {g} p =
  ⊕-intro₁
    {g = g}
    {h = DecProp-grammar' {ℓG = ℓg}((a , yes x))}
    {k = DecProp-grammar' {ℓG = ℓg}(negateDecProp (a , yes x))}
    (⊤-intro {g = g})
    p
DecProp-grammar'-intro {ℓ}{ℓg = ℓg}(a , no ¬x) {g} p =
  ⊕-intro₂
    {g = g}
    {h = DecProp-grammar' {ℓG = ℓg} (negateDecProp (a , no ¬x))}
    {k = DecProp-grammar' {ℓG = ℓg} ((a , no ¬x))}
    (⊤-intro {g = g})
    p

⇒-intro :
  ∀ {ℓ} →
  g ⊢ h →
  ε-grammar {ℓG = ℓ} ⊢ g ⇒ h
⇒-intro e pε pg = e pg

-- TODO what should the implication elim be?
-- ⇒-elim : {!!}
-- ⇒-elim = {!!}

KL*-elim :
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh} →
  ε-grammar {ℓG = ℓh} ⊢ h →
  g ⊗ h ⊢ h →
  KL* g ⊢ h
KL*-elim pε p⊗ (nil x) = pε (lift (lower x))
KL*-elim {g}{h} pε p⊗ (cons x) =
  p⊗ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ (x .snd .snd))))

foldKL*r = KL*-elim

foldKL*l :
  ∀ {ℓg}{ℓh} →
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh} →
  ε-grammar {ℓG = ℓh} ⊢ h →
  h ⊗ g ⊢ h →
  KL* g ⊢ h
foldKL*l {ℓg = ℓg}{ℓh = ℓh}{g = g}{h = h} pε p⊗ =
  trans {g = KL* g} {h = h -⊗ h} {k = h}
    (foldKL*r {g = g} {h = h -⊗ h}
      (-⊗-intro {g = h} {h = ε-grammar {ℓG = ℓh}} {k = h}
        (ε-extension-r {g = ε-grammar {ℓG = ℓh}} {ℓh} {h = h} {k = h}
          (id {g = ε-grammar {ℓG = ℓh}})
          (id {g = h}))
        )
      (-⊗-intro {g = h} {h = g ⊗ (h -⊗ h)} {k = h}
        (trans {g = h ⊗ g ⊗ (h -⊗ h)} {h = (h ⊗ g) ⊗ (h -⊗ h)} {k = h}
          (⊗-assoc-inv {g = h} {h = g} {k = h -⊗ h} {l = (h ⊗ g) ⊗ (h -⊗ h)}
            (id {g = (h ⊗ g) ⊗ (h -⊗ h)}))
          (-⊗-elim {g = h -⊗ h} {h = h} {k = h} {l = h ⊗ g} (id {g = h -⊗ h}) p⊗))
        )
    )
  (trans {g = h -⊗ h} {h = ε-grammar {ℓG = ℓh} ⊗ (h -⊗ h)} {k = h}
    (ε-on-left {g = h -⊗ h} {ℓh})
    (-⊗-elim {g = h -⊗ h} {h = h} {k = h} {l = ε-grammar {ℓG = ℓh}}
      (id {g = h -⊗ h})
      pε))
