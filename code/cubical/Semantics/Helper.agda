module Semantics.Helper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

private
  variable ℓ ℓ' : Level

-- TODO : cubical upstream?
negateDecProp : ∀ {ℓ} → DecProp ℓ → DecProp ℓ
fst (fst (negateDecProp A)) = ¬ A .fst .fst
snd (fst (negateDecProp A)) = isProp→ isProp⊥
snd (negateDecProp A) =
  decRec
    (λ a → no (λ x → x a))
    (λ ¬a → yes ¬a)
    (A .snd)

doubleNegDecProp' :
  ∀ {ℓ} (A : DecProp ℓ) →
  negateDecProp (negateDecProp A) .fst .fst →
  A .fst .fst
doubleNegDecProp' A x = Dec→Stable (A .snd) x

-- TODO : add to cubical?
isSetLift :
  {L L' : Level} →
  {A : Type L} →
  isSet A → isSet (Lift {L}{L'} A)
isSetLift isSetA x y a b i =
  liftExt
    (isSetA (lower x) (lower y)
    (cong lower a) (cong lower b) i)

discreteLift :
  {L L' : Level} →
  {A : Type L} →
  Discrete A → Discrete (Lift {L}{L'} A)
discreteLift discreteA x y =
  decRec
    (λ lx≡ly → yes (liftExt lx≡ly))
    (λ lx≢ly → no (λ p → lx≢ly (cong lower p)))
    (discreteA (lower x) (lower y))

isFinSetLift :
  {L L' : Level} →
  {A : Type L} →
  isFinSet A → isFinSet (Lift {L}{L'} A)
fst (isFinSetLift {A = A} isFinSetA) = isFinSetA .fst
snd (isFinSetLift {A = A} isFinSetA) =
  Cubical.HITs.PropositionalTruncation.elim
  {P = λ _ → ∥ Lift A ≃ Fin (isFinSetA .fst) ∥₁}
  (λ [a] → isPropPropTrunc )
  (λ A≅Fin → ∣ compEquiv (invEquiv (LiftEquiv {A = A})) A≅Fin ∣₁)
  (isFinSetA .snd)

isPropCod→isProp≃ :
  {a : Type ℓ}{b : Type ℓ'} →
  isProp b → isProp (a ≃ b)
isPropCod→isProp≃ isPropB =
  isPropΣ
    (isProp→ isPropB)
    λ f → isPropIsEquiv f

open Iso
DecPropIso : ∀ {ℓ} → Iso (DecProp ℓ) (DecProp' ℓ)
fun DecPropIso x =
  decRec
    (λ y → x .fst .fst ,
      (true , isContr→Equiv (y , x .fst .snd y) isContrUnit))
    (λ ¬y → x .fst .fst , (false , uninhabEquiv ¬y (λ x → x)))
    (x .snd)
fst (fst (inv DecPropIso (a , b , c))) = a
snd (fst (inv DecPropIso (a , b , c))) = isDecProp→isProp (b , c)
snd (inv DecPropIso (a , false , c)) =
  no (equivToIso c .fun)
snd (inv DecPropIso (a , true , c)) =
  yes (equivToIso c .inv tt)
rightInv DecPropIso (a , false , c) =
  ΣPathP (refl , (ΣPathP (refl ,
    isPropCod→isProp≃ isProp⊥ _ c )))
rightInv DecPropIso (a , true , c) =
  ΣPathP (refl , (ΣPathP (refl ,
    isPropCod→isProp≃ isPropUnit _ c)))
leftInv DecPropIso (A , yes p) =
  Σ≡Prop (λ x → isPropDec (x .snd))
    (ΣPathP (refl , (isPropIsProp _ _)))
leftInv DecPropIso (A , no ¬p) =
  Σ≡Prop (λ x → isPropDec (x .snd))
    (ΣPathP (refl , (isPropIsProp _ _)))
