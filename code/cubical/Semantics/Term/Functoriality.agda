open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Term.Functoriality ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term.Base (Σ₀ , isSetΣ₀)
open import Semantics.Term.Rules (Σ₀ , isSetΣ₀)

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

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
  ⊕-elim {g = x [ g ]fEval}{h = (x [ h ]fEval) ⊕ l}{k = l}
    (seq {h = ( x [ h ]fEval)}
      (functoriality {g = g}{h = h} x g⊢h)
      (⊕-inl {g = x [ h ]fEval}{h = l}))
    (⊕-inr {g = l}{h = x [ h ]fEval})
functoriality {g = g}{h = h} (l ⊕r x) g⊢h =
  ⊕-elim {g = l}{h = l ⊕ (x [ h ]fEval)}{k = x [ g ]fEval}
    (⊕-inl {g = l}{h = x [ h ]fEval})
    (seq {h = ( x [ h ]fEval)}
      (functoriality {g = g}{h = h} x g⊢h)
      (⊕-inr {g = x [ h ]fEval}{h = l}))
functoriality {g = g}{h = h} (x ⊗OH y) g⊢h =
   (⊗-intro {g = evalFunctorialExpr x g} {h = evalFunctorialExpr x h}
     {k = evalFunctorialExpr y g} {l = evalFunctorialExpr y h}
     (functoriality {g = g} {h = h}  x g⊢h)
     (functoriality {g = g} {h = h}  y g⊢h))
functoriality {g = g}{h = h} (x ⊕OH y) g⊢h =
  ⊕-elim {g = x [ g ]fEval}{h = (x [ h ]fEval) ⊕ (y [ h ]fEval)}{k = y [ g ]fEval}
    (seq {h = x [ h ]fEval}
      (functoriality {g = g}{h = h} x g⊢h)
      (⊕-inl {g = x [ h ]fEval}{h = y [ h ]fEval}))
    (seq {h = y [ h ]fEval}
      (functoriality {g = g}{h = h} y g⊢h)
      (⊕-inr {g = y [ h ]fEval}{h = x [ h ]fEval}))
functoriality {g = g}{h = h} (l -⊗OH x) g⊢h =
   -⊗-intro {g = l} {h = l -⊗ (x [ g ]fEval)} {k = x [ h ]fEval}
     (seq {g = l ⊗ (l -⊗ (x [ g ]fEval))} {h = x [ g ]fEval} {k = x [ h ]fEval}
       -⊗-app
       (functoriality {g = g} {h = h} x g⊢h))
functoriality {g = g}{h = h} (x ⊗-OH l) g⊢h =
  ⊗--intro {g = (x [ g ]fEval) ⊗- l}{h = l}{k = x [ h ]fEval}
     (seq {g = ((x [ g ]fEval) ⊗- l) ⊗ l} {h = x [ g ]fEval} {k = x [ h ]fEval}
       ⊗--app
       (functoriality {g = g} {h = h} x g⊢h))

⊗-seq-l' :
  g ⊢ h  →
  h ⊗ k ⊢ l →
  g ⊗ k ⊢ l
⊗-seq-l' {g = g}{h = h}{k = k}{l = l} e e' =
  seq {g = g ⊗ k} {h = h ⊗ k} { k = l }
  (functoriality {g = g} {h = h} (var ⊗l k) e)
  e'

functoriality-test :
  {g h j k l m n o p q : Grammar ℓg} →
  g ⊢ h →
  j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h)))) ⊢ q →
  j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g)))) ⊢ q
functoriality-test {g = g}{h}{j}{k}{l}{m}{n}{o}{p}{q} e e' =
  seq {g = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ g))))}
   {h = j -⊗ (k -⊗ (l ⊗ (m ⊕ (p -⊗ h))))} {k = q}
   (functoriality {g = g} {h = h}
     (j -⊗OH (k -⊗OH (l ⊗r (m ⊕r (p -⊗OH var)))))
     e)
   e'
