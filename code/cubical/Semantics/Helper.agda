module Semantics.Helper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
import Cubical.Data.Fin as Fin
import Cubical.Data.Fin.Arithmetic as Arith
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

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

isPropLift :
  {L L' : Level} →
  {A : Type L} →
  isProp A → isProp (Lift {L}{L'} A)
isPropLift x a b = liftExt (x _ _)

-- TODO : add to cubical?
isSetLift :
  {L L' : Level} →
  {A : Type L} →
  isSet A → isSet (Lift {L}{L'} A)
isSetLift isSetA x y a b i =
  liftExt
    (isSetA (lower x) (lower y)
    (cong lower a) (cong lower b) i)

DecLift :
  {L L' : Level} →
  {A : Type L} →
  Dec A → Dec (Lift {L}{L'} A)
DecLift {L} {L'} {A} (yes p) = yes (lift p)
DecLift {L} {L'} {A} (no ¬p) = no (λ x → ¬p (lower x))

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
  PT.elim
  {P = λ _ → ∥ Lift A ≃ Fin (isFinSetA .fst) ∥₁}
  (λ [a] → isPropPropTrunc )
  (λ A≅Fin → ∣ compEquiv (invEquiv (LiftEquiv {A = A})) A≅Fin ∣₁)
  (isFinSetA .snd)

LiftList : ∀ {L}{L'} → {A : Type L} → List A → List (Lift {L}{L'} A)
LiftList [] = []
LiftList (x ∷ xs) = lift x ∷ LiftList xs

LiftListDist : ∀ {L}{L'} {A : Type L} (w w' : List A) →
  LiftList {L}{L'} (w ++ w') ≡ (LiftList {L}{L'} w) ++ (LiftList {L}{L'} w')
LiftListDist [] w' = refl
LiftListDist (x ∷ w) w' = cong (lift x ∷_) (LiftListDist w w')

isFinOrdFin : ∀ {n} → isFinOrd (Fin n)
isFinOrdFin {n} = n , (idEquiv (Fin n))

isFinOrd⊥ : isFinOrd ⊥
fst isFinOrd⊥ = 0
snd isFinOrd⊥ = idEquiv ⊥

takeFirstFinOrd : ∀ {ℓ} → (A : Type ℓ) → (the-ord : isFinOrd A) → 0 Ord.< the-ord .fst → A
takeFirstFinOrd A (suc n , the-eq) x =
  the-eq .snd .equiv-proof (Fin→SumFin (Fin.fromℕ≤ 0 n x)) .fst .fst

isPropCod→isProp≃ :
  {a : Type ℓ}{b : Type ℓ'} →
  isProp b → isProp (a ≃ b)
isPropCod→isProp≃ isPropB =
  isPropΣ
     (isProp→ isPropB)
    λ f → isPropIsEquiv f

open Iso
DecPropIso : ∀ {ℓ} → Iso (DecProp ℓ) (DecProp' ℓ)
fun DecPropIso (a , yes p) =
  (a .fst) ,
  (true , (isContr→Equiv (p , λ y → a .snd _ _) isContrUnit))
fun DecPropIso (a , no ¬p) = (a .fst) , ((false , uninhabEquiv ¬p (λ x → x)))
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

DecProp≃DecProp' : ∀ {ℓ} → DecProp ℓ ≃ DecProp' ℓ
DecProp≃DecProp' = isoToEquiv DecPropIso

DecProp'→DecProp : ∀ {ℓ} → DecProp' ℓ → DecProp ℓ
DecProp'→DecProp = DecPropIso .inv

DecProp→DecProp' : ∀ {ℓ} → DecProp ℓ → DecProp' ℓ
DecProp→DecProp' = DecPropIso .fun

DecProp'Witness→DecPropWitness :
  ∀ {ℓ} → (A : DecProp' ℓ) → (a : A .fst) →
   DecProp'→DecProp A .fst .fst 
DecProp'Witness→DecPropWitness (u , false , r) a =
  ⊥.rec (r .fst a)
DecProp'Witness→DecPropWitness (u , true , r) a = a

DecPropWitness→DecPropWitness' :
  ∀ {ℓ} → (A : DecProp ℓ) → (a : A .fst .fst) →
   DecProp→DecProp' A .fst
DecPropWitness→DecPropWitness' (a , yes p) c = c
DecPropWitness→DecPropWitness' (a , no ¬p) c = ⊥.rec (¬p c)

DecProp⊎ :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : DecProp ℓ) →
  (A .fst .fst → B .fst .fst → ⊥) → DecProp ℓ
fst (fst (DecProp⊎ A B AB→⊥)) = A .fst .fst ⊎ B .fst .fst
snd (fst (DecProp⊎ A B AB→⊥)) =
  isProp⊎ (A .fst .snd) (B .fst .snd) AB→⊥
snd (DecProp⊎ A B AB→⊥) =
  decRec
    (λ a → yes (inl a))
    (λ ¬a →
      decRec
        (λ b → yes (inr b))
        (λ ¬b → no (Cubical.Data.Sum.rec ¬a ¬b))
        (B .snd))
    (A .snd)

DecPropΣ :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : A .fst .fst → DecProp ℓ) →
  DecProp ℓ
fst (fst (DecPropΣ A B)) = Σ[ a ∈ A .fst .fst ] B a .fst .fst
snd (fst (DecPropΣ A B)) = isPropΣ (A .fst .snd) (λ a → B a .fst .snd)
snd (DecPropΣ A B) =
  decRec
    (λ a →
    decRec
      (λ ba → yes (a , ba))
      (λ ¬ba →
        no (λ x →
          ¬ba (transport
            (cong (λ c → B c .fst .fst) (A .fst .snd _ _)) (x .snd) )))
      (B a .snd))
    (λ ¬a → no (λ x → ¬a (x .fst)))
    (A .snd)

-- inhabDecRec :
--    ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} →
--    (ifyes : P → Type) → (ifno : ¬ P → Type) →
--    (a : Dec P) → decRec ifyes ifno a
-- inhabDecRec ifyes ifno (yes p) = {!!}
-- inhabDecRec ifyes ifno (no ¬p) = {!!}

DecProp× :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : DecProp ℓ) →
  DecProp ℓ
DecProp× A B = DecPropΣ A (λ _ → B)

Bool-iso-DecProp' : ∀ {ℓ} → Iso (Bool) (DecProp' ℓ)
fst (fun Bool-iso-DecProp' false) = ⊥*
fst (fun Bool-iso-DecProp' true) = Unit*
snd (fun Bool-iso-DecProp' false) = false , (uninhabEquiv lower (λ x → x))
snd (fun Bool-iso-DecProp' true) = true , (isContr→Equiv isContrUnit* isContrUnit)
inv Bool-iso-DecProp' (a , false , c) = false
inv Bool-iso-DecProp' (a , true , c) = true
rightInv Bool-iso-DecProp' (a , false , c) =
  ΣPathP
    (sym (ua (compEquiv c ⊥≃⊥*)) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y → Σ≡Prop isPropIsEquiv (isProp→ isProp⊥ _ _)) _ _)))
  where
  ⊥≃⊥* : ⊥ ≃ ⊥*
  ⊥≃⊥* = uninhabEquiv (λ x → x) lower
rightInv Bool-iso-DecProp' (a , true , c) =
  ΣPathP
    ((sym (ua (compEquiv c Unit≃Unit*))) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y → Σ≡Prop isPropIsEquiv (isProp→ isPropUnit _ _)) _ _)))
leftInv Bool-iso-DecProp' false = refl
leftInv Bool-iso-DecProp' true = refl

Bool≃DecProp' : ∀ {ℓ} → Bool ≃ DecProp' ℓ
Bool≃DecProp' = isoToEquiv Bool-iso-DecProp'

Bool≃DecProp : ∀ {ℓ} → Bool ≃ DecProp ℓ
Bool≃DecProp = compEquiv Bool≃DecProp' (invEquiv DecProp≃DecProp')

isFinSetDecProp : ∀ {ℓ} → isFinSet (DecProp ℓ)
fst isFinSetDecProp = 2
snd isFinSetDecProp = ∣ the-equiv ∣₁
  where
  the-equiv : DecProp ℓ ≃ Fin 2
  the-equiv = compEquiv (invEquiv Bool≃DecProp) (invEquiv SumFin2≃Bool)

Decℙ : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
Decℙ {ℓ} A = A → DecProp ℓ

Decℙ' : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
Decℙ' {ℓ} A = A → DecProp' ℓ

LiftDecProp :
  ∀ {L}{L'} →
  DecProp L →
  DecProp (ℓ-max L L')
LiftDecProp {L} {L'} (a , yes p) =
  ((Lift {L}{L'} (a .fst)) , (isPropLift (a .snd))) , (yes (lift p))
LiftDecProp {L} {L'} (a , no ¬p) =
  ((Lift {L}{L'} (a .fst)) , (isPropLift (a .snd))) , (no λ x → ¬p (lower x))

LiftDecProp' :
  ∀ {L}{L'} →
  DecProp' L →
  DecProp' (ℓ-max L L')
LiftDecProp' {L} {L'} (a , false , c) = (Lift {L}{L'} a) , (false , (compEquiv (invEquiv LiftEquiv) c))
LiftDecProp' {L} {L'} (a , true , c) = (Lift {L}{L'} a) , (true , (compEquiv (invEquiv LiftEquiv) c))

LiftDecProp'Witness :
  ∀ {L}{L'} →
  (A : DecProp' L) →
  (a : A .fst) →
  LiftDecProp' {L}{L'} A .fst
LiftDecProp'Witness {L}{L'} (u , false , v) a = lift {L}{L'} a
LiftDecProp'Witness {L}{L'} (u , true , v) a = lift {L}{L'} a

LowerDecProp'Witness :
  ∀ {L}{L'} →
  (A : DecProp' L) →
  (a : LiftDecProp' {L}{L'} A .fst) →
  A .fst
LowerDecProp'Witness {L}{L'} (u , false , v) a = lower a
LowerDecProp'Witness {L}{L'} (u , true , v) a = lower a

LiftDecℙ' : ∀ {L}{L'} (A : Type L) →
  (Decℙ' {L} A) → (Decℙ' {ℓ-max L L'} (Lift {L}{L'} A))
LiftDecℙ' {L}{L'} A x a = LiftDecProp' {L}{L'} (x (lower a))

DecℙIso : ∀ {ℓ} (A : Type ℓ) → Iso (Decℙ A) (Decℙ' A)
fun (DecℙIso A) x a = DecPropIso .fun (x a)
inv (DecℙIso A) x' a = DecPropIso .inv (x' a)
rightInv (DecℙIso A) b =
  funExt (λ x → DecPropIso .rightInv _)
leftInv (DecℙIso A) a =
  funExt (λ x → DecPropIso .leftInv _)

inDecℙ :
  ∀ {ℓ} → {A : Type ℓ} →
  (a : A) → Decℙ A → Type ℓ
inDecℙ a X = X a .fst .fst

isFinSetDecℙ : ∀ {ℓ} → (A : FinSet ℓ) → isFinSet (Decℙ (A .fst))
isFinSetDecℙ {ℓ} A = isFinSet→ A (DecProp ℓ , isFinSetDecProp)

isFinSetDecℙ' : ∀ {ℓ} → (A : FinSet ℓ) → isFinSet (Decℙ' (A .fst))
isFinSetDecℙ' A =
  PT.rec
    isPropIsFinSet
    (λ the-eq →
      (isFinSetDecℙ A .fst) ,
      ∣ compEquiv (isoToEquiv (invIso (DecℙIso (A .fst)))) the-eq ∣₁)
    (isFinSetDecℙ A .snd)

FinSetDecℙ : ∀ {ℓ} → FinSet ℓ → FinSet (ℓ-suc ℓ)
FinSetDecℙ {ℓ} A = (Decℙ (A .fst)) , (isFinSetDecℙ A)

FinSetDecℙ' : ∀ {ℓ} → FinSet ℓ → FinSet (ℓ-suc ℓ)
FinSetDecℙ' {ℓ} A = (Decℙ' (A .fst)) , (isFinSetDecℙ' A)

SingletonDecℙ : ∀ {ℓ} {A : FinSet ℓ} → (a : A .fst) → Decℙ (A .fst)
SingletonDecℙ {A = A} a x =
  ((x ≡ a) ,
  isFinSet→isSet (A .snd) _ _) ,
  isFinSet→Discrete (A .snd) _ _

SingletonDecℙ' : ∀ {ℓ} {A : FinSet ℓ} → (a : A .fst) → Decℙ' (A .fst)
SingletonDecℙ' {A = A} a =
  DecℙIso (A .fst) .fun (SingletonDecℙ {A = A} a)
