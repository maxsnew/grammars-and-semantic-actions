open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Term ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

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
open import Semantics.Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

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

syntax -⊗-intro {g = g} e = λ-⊗[ x ∈ g ][ e ]

-⊗-elim :
  g ⊗ (g -⊗ h) ⊢ h
-⊗-elim {h = h} p =
  transport
    (cong h (sym (p .fst .snd)))
    (p .snd .snd (fst p .fst .fst) (p .snd .fst))

syntax -⊗-elim {g = g}{h = h} = app[ g -⊗ h ]

-- -⊗-β :
--   (e : g ⊗ h ⊢ k) →
--   (e' : l ⊢ g) →
--   Term≡ {Σ₀}
--     (e' -⊗app[ g -⊗ k ] λ-⊗[ x ∈ g ][ e ])
--     (λ x → e (x .fst , ((e' (x .snd .fst)) , (x .snd .snd))))
-- -⊗-β e e' p = {!!}


⊗--intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⊗- h
⊗--intro e p w' q =
  e ((_ , refl) , p , q)

syntax ⊗--intro {h = h} e = λ⊗-[ x ∈ h ][ e ]

⊗--elim :
  (h ⊗- g) ⊗ g ⊢ h
⊗--elim {h = h} p =
  transport
    (cong h (sym (p .fst .snd)))
    (p .snd .fst (fst p .fst .snd) (p .snd .snd))

syntax ⊗--elim {g = g}{h = h} = app[ h ⊗- g ]

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

-- The following type allows us to induct over well-behaved contexts to build a
-- powerful functoriality principle
-- We wish to define something like:
--    functoriality :
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
-- because without use of it, we must manually conjugate with the introduction and elimination forms
--
-- Instead below we do this work once
data FunctorialExpression : (L : Level) → Typeω where
  var : FunctorialExpression ℓ-zero
  _⊗l_ : ∀ {L}{L'} → FunctorialExpression L' → Grammar L → FunctorialExpression (ℓ-max L L')
  _⊗r_ : ∀ {L}{L'} → Grammar L → FunctorialExpression L' → FunctorialExpression  (ℓ-max L L')
  _⊕l_ : ∀ {L}{L'} → FunctorialExpression L' → Grammar  L  → FunctorialExpression (ℓ-max L L')
  _⊕r_ : ∀ {L}{L'} → Grammar L → FunctorialExpression L' → FunctorialExpression (ℓ-max L L')
  _⊗OH_ : ∀ {L} {L'} → FunctorialExpression L → FunctorialExpression L' → FunctorialExpression (ℓ-max L L')
  _⊕OH_ : ∀ {L} {L'} → FunctorialExpression L → FunctorialExpression L' → FunctorialExpression (ℓ-max L L')
  _-⊗OH_ : ∀ {L} {L'} → Grammar L  → FunctorialExpression L' → FunctorialExpression (ℓ-max L L')
  _⊗-OH_ : ∀ {L} {L'} → FunctorialExpression L  → Grammar L' → FunctorialExpression (ℓ-max L L')

evalFunctorialExpr : ∀ {L} {L'} → FunctorialExpression L → Grammar L' → Grammar (ℓ-max L L')
evalFunctorialExpr var g = g
evalFunctorialExpr (x ⊗l h) g = (evalFunctorialExpr x g) ⊗ h
evalFunctorialExpr (h ⊗r x) g = h ⊗ evalFunctorialExpr x g
evalFunctorialExpr (x ⊕l h) g = (evalFunctorialExpr x g) ⊕ h
evalFunctorialExpr (h ⊕r x) g = h ⊕ evalFunctorialExpr x g
evalFunctorialExpr (x ⊗OH y) g = (evalFunctorialExpr x g) ⊗ (evalFunctorialExpr y g)
evalFunctorialExpr (x ⊕OH y) g = (evalFunctorialExpr x g) ⊕ (evalFunctorialExpr y g)
evalFunctorialExpr (h -⊗OH x) g = h -⊗ (evalFunctorialExpr x g)
evalFunctorialExpr (x ⊗-OH h) g = (evalFunctorialExpr x g) ⊗- h

syntax evalFunctorialExpr Δ g = Δ [ g ]fEval

functoriality :
  (Δ : FunctorialExpression ℓg) →
  g ⊢ h →
  Δ [ g ]fEval ⊢ Δ [ h ]fEval
functoriality {g = g}{h = h} var g⊢h = g⊢h
functoriality {g = g}{h = h} (x ⊗l l) g⊢h =
  ⊗-intro {g =  evalFunctorialExpr x g} {h = evalFunctorialExpr x h} {k = l}{l = l}
    (functoriality {g = g} {h = h} x g⊢h)
    (id {g = l})
functoriality {g = g}{h = h} (l ⊗r x) g⊢h =
  ⊗-intro {g = l} {h = l} {k = evalFunctorialExpr x g}
   {l = evalFunctorialExpr x h}
   (id {g = l})
   (functoriality {g = g}{h = h } x g⊢h)
functoriality {g = g}{h = h} (x ⊕l l) g⊢h =
  ⊕-elim {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h ⊕ l}
   (⊕-intro₁ {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h} {k = l}
     (functoriality {g = g}{h = h} x g⊢h))
   (⊕-intro₂ {g = l} {h = l} {k = evalFunctorialExpr x h} (id {g = l}))
functoriality {g = g}{h = h} (l ⊕r x) g⊢h =
  ⊕-elim {g = l} {h = l ⊕ evalFunctorialExpr x h}
   (⊕-intro₁ {g = l} {h = l} {k = evalFunctorialExpr x h} (id {g = l}))
   (⊕-intro₂ {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h} {k = l}
     (functoriality {g = g}{h = h} x g⊢h))
functoriality {g = g}{h = h} (x ⊗OH y) g⊢h =
   (⊗-intro {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h}
     {k = evalFunctorialExpr y g} {l = evalFunctorialExpr y h}
     (functoriality {g = g} {h = h}  x g⊢h)
     (functoriality {g = g} {h = h}  y g⊢h)
     )
functoriality {g = g}{h = h} (x ⊕OH y) g⊢h =
   (⊕-elim {g = evalFunctorialExpr x g}
     {h = evalFunctorialExpr x h ⊕ evalFunctorialExpr y h} {k = evalFunctorialExpr y g}
     (⊕-intro₁ {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h}
       {k = evalFunctorialExpr y h} (functoriality {g = g}{h = h} x g⊢h )
     )
     (⊕-intro₂ {g = evalFunctorialExpr y g} {h = evalFunctorialExpr y h}
       {k = evalFunctorialExpr x h} (functoriality {g = g}{h = h} y g⊢h )
     )
     )
functoriality {g = g}{h = h} (l -⊗OH x) g⊢h =
   -⊗-intro {g = l} {h = l -⊗ (x [ g ]fEval)} {k = x [ h ]fEval}
     (seq {g = l ⊗ (l -⊗ (x [ g ]fEval))} {h = x [ g ]fEval} {k = x [ h ]fEval}
       -⊗-elim
       (functoriality {g = g} {h = h} x g⊢h))
functoriality {g = g}{h = h} (x ⊗-OH l) g⊢h =
  ⊗--intro {g = (x [ g ]fEval) ⊗- l}{h = l}{k = x [ h ]fEval}
     (seq {g = ((x [ g ]fEval) ⊗- l) ⊗ l} {h = x [ g ]fEval} {k = x [ h ]fEval}
       ⊗--elim
       (functoriality {g = g} {h = h} x g⊢h))

-- ⊗-trans-l' :
--   g ⊢ h  →
--   h ⊗ k ⊢ l →
--   g ⊗ k ⊢ l
-- ⊗-trans-l' {g = g}{h = h}{k = k}{l = l} e e' =
--   trans {g = g ⊗ k} {h = h ⊗ k} { k = l }
--   (functoriality {g = g} {h = h} (var ⊗l k) e)
--   e'

-- functoriality-test :
--   {g h j k l m n o p q : Grammar ℓg} →
--   g ⊢ h →
--   j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h)))) ⊢ q →
--   j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g)))) ⊢ q
-- functoriality-test {g = g}{h}{j}{k}{l}{m}{n}{o}{p}{q} e e' =
--   trans {g = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g))))}
--    {h = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h))))} {k = q}
--    (functoriality {g = g} {h = h}
--      (j -⊗OH (k -⊗OH (l ⊗r (m ⊕r (p -⊗OH var)))))
--      e)
--    e'

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

-- ⇒-intro :
--   g ⊢ h →
--   ε-grammar ⊢ g ⇒ h
-- ⇒-intro e pε pg = e pg

-- -- TODO what should the implication elim be?
-- -- ⇒-elim : {!!}
-- -- ⇒-elim = {!!}

-- KL*-elim :
--   ε-grammar ⊢ h →
--   g ⊗ h ⊢ h →
--   KL* g ⊢ h
-- KL*-elim pε p⊗ (nil x) = pε x
-- KL*-elim {g}{h} pε p⊗ (cons x) =
--   p⊗ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ (x .snd .snd))))

-- foldKL*r = KL*-elim

-- foldKL*l :
--   {g : Grammar ℓg} →
--   {h : Grammar ℓh} →
--   ε-grammar ⊢ h →
--   h ⊗ g ⊢ h →
--   KL* g ⊢ h
-- foldKL*l {g = g}{h = h} pε p⊗ =
--   trans {g = KL* g} {h = h -⊗ h} {k = h}
--     (foldKL*r
--       (-⊗-intro {g = h} {h = ε-grammar} {k = h}
--         (ε-extension-r {g = ε-grammar} {h = h} {k = h}
--           (id {g = ε-grammar })
--           (id {g = h}))
--         )
--       (-⊗-intro {g = h} {h = g ⊗ (h -⊗ h)} {k = h}
--         (trans {g = h ⊗ g ⊗ (h -⊗ h)} {h = (h ⊗ g) ⊗ (h -⊗ h)} {k = h}
--           (⊗-assoc-inv {g = h} {h = g} {k = h -⊗ h} {l = (h ⊗ g) ⊗ (h -⊗ h)}
--             (id {g = (h ⊗ g) ⊗ (h -⊗ h)}))
--           (-⊗-elim {g = h -⊗ h} {h = h} {k = h} {l = h ⊗ g} (id {g = h -⊗ h}) p⊗))
--         )
--     )
--   (trans {g = h -⊗ h} {h = ε-grammar ⊗ (h -⊗ h)} {k = h}
--     (ε-on-left {g = h -⊗ h})
--     (-⊗-elim {g = h -⊗ h} {h = h} {k = h} {l = ε-grammar }
--       (id {g = h -⊗ h})
--       pε))

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
