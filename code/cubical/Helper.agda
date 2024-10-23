{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Helper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Function.More

open import Cubical.Relation.Binary.Order.Loset
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.FinData.More using (DecΣ ; Fin≡SumFin ; Fin≃Finℕ ; Fin≃SumFin)
import Cubical.Data.FinData as FD

import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.Bool as Bool hiding (_⊕_; _≤_)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
import Cubical.Data.Fin as Fin
import Cubical.Data.Fin.Arithmetic as Arith
import Cubical.Data.Equality as Eq
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

isGroupoidLift :
  {L L' : Level} →
  {A : Type L} →
  isGroupoid A → isGroupoid (Lift {L}{L'} A)
isGroupoidLift isGroupoidA x y a b u v i j k =
  lift
  ((isGroupoidA (lower x) (lower y)) (cong lower a)
    (cong lower b) (cong (cong lower) u) (cong (cong lower) v) i j k)

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

LowerList : ∀ {L}{L'} → {A : Type L} → List (Lift {L}{L'} A) → List A
LowerList [] = []
LowerList (x ∷ xs) = lower x ∷ LowerList xs

LiftListDist : ∀ {L}{L'} {A : Type L} (w w' : List A) →
  LiftList {L}{L'} (w ++ w') ≡ (LiftList {L}{L'} w) ++ (LiftList {L}{L'} w')
LiftListDist [] w' = refl
LiftListDist (x ∷ w) w' = cong (lift x ∷_) (LiftListDist w w')

EquivPresIsFinOrd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → isFinOrd A → isFinOrd B
EquivPresIsFinOrd e (_ , p) = _ , compEquiv (invEquiv e) p

isFinOrdFin : ∀ {n} → isFinOrd (Fin n)
isFinOrdFin {n} = n , (idEquiv (Fin n))

isFinOrd⊥ : isFinOrd ⊥
fst isFinOrd⊥ = 0
snd isFinOrd⊥ = idEquiv ⊥

takeFirstFinOrd : ∀ {ℓ} → (A : Type ℓ) →
  (the-ord : isFinOrd A) → 0 Ord.< the-ord .fst → A
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
DecPropIso .fun (A , dec) = ⟨ A ⟩ , decRec
  (λ a → true , isContr→Equiv (a , λ y → str A _ _) isContrUnit)
  (λ ¬a → false , uninhabEquiv ¬a (λ x → x))
  dec
DecPropIso .inv (A , isDecPropA) =
  (A , isDecProp→isProp isDecPropA) , isDecProp→Dec isDecPropA
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

DecProp≡DecProp' : ∀ {ℓ} → DecProp ℓ ≡ DecProp' ℓ
DecProp≡DecProp' = isoToPath DecPropIso

DecPropFstPath : ∀ {ℓ} → (A : DecProp ℓ) →
  A .fst .fst ≡ (DecPropIso .fun A) .fst
DecPropFstPath (a , yes p) = refl
DecPropFstPath (a , no ¬p) = refl

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

DecProp→FinSet : ∀ {ℓ} (P : DecProp ℓ) → FinSet ℓ
DecProp→FinSet P = ⟨ P .fst ⟩ , isDecProp→isFinSet (str (P .fst)) (P .snd)

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
        (λ ¬b → no (Sum.rec ¬a ¬b))
        (B .snd))
    (A .snd)

DecProp'∃ : ∀ {L}{L'} → (X : FinSet L)
  (P : X .fst → DecProp' L')  → DecProp' (ℓ-max L L')
DecProp'∃ X P = (∃[ x ∈ X .fst ] P x .fst) , (isDecProp∃  X P)

DecProp∃ : ∀ {L}{L'} → (X : FinSet L)
  (P : X .fst → DecProp L')  → DecProp (ℓ-max L L')
DecProp∃ X P =
  ((∃[ x ∈ X .fst ] P x .fst .fst) , isPropPropTrunc) ,
    DecProp'→DecProp (∥ Σ (X .fst) (λ x → P x .fst .fst) ∥₁ ,
                     isDecProp∃ X λ x → P x .fst .fst ,
                     transport (cong isDecProp (sym (DecPropFstPath (P x))))
                     (DecProp→DecProp' (P x) .snd)) .snd
-- -- (∃[ x ∈ X .fst ] P x .fst) , (isDecProp∃  X P)
-- --

DecProp'∀ :
  ∀ {ℓ ℓ'} (X : FinSet ℓ) (P : ⟨ X ⟩ → DecProp' ℓ') →
  DecProp' (ℓ-max ℓ ℓ')
DecProp'∀ X P = ((x : ⟨ X ⟩) → ⟨ P x ⟩) , (isDecProp∀ X P)

DecProp∀ :
  ∀ {ℓ ℓ'} (X : FinSet ℓ) (P : ⟨ X ⟩ → DecProp ℓ') →
  DecProp (ℓ-max ℓ ℓ')
DecProp∀ X P = DecProp'→DecProp (DecProp'∀ X (DecProp→DecProp' ∘ P))

DecProp→ :
  ∀ {ℓ ℓ'} (P : DecProp ℓ) (Q : DecProp ℓ') →
  DecProp (ℓ-max ℓ ℓ')
DecProp→ P Q = DecProp∀ (DecProp→FinSet P) (λ _ → Q)

DecPropΣProp :
  ∀ {ℓ ℓ'} (A : FinSet ℓ) (B : ⟨ A ⟩ → DecProp ℓ')
  (unique : (x y : ⟨ A ⟩) → ⟨ B x .fst ⟩ → ⟨ B y .fst ⟩ → x ≡ y) →
  DecProp (ℓ-max ℓ ℓ')
DecPropΣProp A B unique =
  let C = Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a .fst ⟩ in
  let isPropC = λ (x , Bx) (y , By) → Σ≡Prop (λ a → str (B a .fst)) (unique x y Bx By) in
  (C , isPropC) ,
  mapDec
    (PT.rec isPropC (λ x → x))
    (λ ¬c c → ¬c ∣ c ∣₁)
    (DecProp∃ A B .snd)

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

DecProp'× :
  ∀ {ℓ} → (A : DecProp' ℓ) → (B : DecProp' ℓ) → DecProp' ℓ
DecProp'× A B = (A .fst × B .fst) , (isDecProp× A B)

DecProp≡ : ∀ {ℓ} {A : Type ℓ} → Discrete A → A → A → DecProp ℓ
DecProp≡ disc x y = ((x ≡ y) , Discrete→isSet disc x y) , disc x y

Bool-iso-DecProp' : ∀ {ℓ} → Iso (Bool) (DecProp' ℓ)
fst (fun Bool-iso-DecProp' false) = ⊥*
fst (fun Bool-iso-DecProp' true) = Unit*
snd (fun Bool-iso-DecProp' false) =
  false , (uninhabEquiv lower (λ x → x))
snd (fun Bool-iso-DecProp' true) =
  true , (isContr→Equiv isContrUnit* isContrUnit)
inv Bool-iso-DecProp' (a , false , c) = false
inv Bool-iso-DecProp' (a , true , c) = true
rightInv Bool-iso-DecProp' (a , false , c) =
  ΣPathP
    (sym (ua (compEquiv c ⊥≃⊥*)) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y →
          Σ≡Prop isPropIsEquiv (isProp→ isProp⊥ _ _)) _ _)))
  where
  ⊥≃⊥* : ⊥ ≃ ⊥*
  ⊥≃⊥* = uninhabEquiv (λ x → x) lower
rightInv Bool-iso-DecProp' (a , true , c) =
  ΣPathP
    ((sym (ua (compEquiv c Unit≃Unit*))) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y →
          Σ≡Prop isPropIsEquiv (isProp→ isPropUnit _ _)) _ _)))
leftInv Bool-iso-DecProp' false = refl
leftInv Bool-iso-DecProp' true = refl

Bool≃DecProp' : ∀ {ℓ} → Bool ≃ DecProp' ℓ
Bool≃DecProp' = isoToEquiv Bool-iso-DecProp'

Bool≃DecProp : ∀ {ℓ} → Bool ≃ DecProp ℓ
Bool≃DecProp = compEquiv Bool≃DecProp' (invEquiv DecProp≃DecProp')

Bool-iso-DecProp'-witness→truth :
  ∀ {ℓ} →
  (b : Bool) →
  Bool-iso-DecProp' {ℓ = ℓ} .fun b .fst →
  true Eq.≡ b
Bool-iso-DecProp'-witness→truth true witness = Eq.refl

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

LiftDecProp'' :
  ∀ {L}{L'} →
  DecProp L →
  DecProp (ℓ-max L L')
LiftDecProp'' {L} {L'} (p , _) .fst .fst = Lift {L}{L'} (p .fst)
LiftDecProp'' {L} {L'} (p , _) .fst .snd = isPropLift (p .snd)
LiftDecProp'' (p , yes yep) .snd = yes (lift yep)
LiftDecProp'' (p , no nope) .snd = no (λ lyep → nope (lyep .lower))

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
LiftDecProp' {L} {L'} (a , false , c) =
  (Lift {L}{L'} a) , (false , (compEquiv (invEquiv LiftEquiv) c))
LiftDecProp' {L} {L'} (a , true , c) =
  (Lift {L}{L'} a) , (true , (compEquiv (invEquiv LiftEquiv) c))

LiftDecProp'Witness :
  ∀ {L}{L'} →
  (A : DecProp' L) →
  (a : A .fst) →
  LiftDecProp' {L}{L'} A .fst
LiftDecProp'Witness {L}{L'} (u , false , v) a = lift {L}{L'} a
LiftDecProp'Witness {L}{L'} (u , true , v) a = lift {L}{L'} a

LiftDecPropWitness :
  ∀ {L}{L'} →
  (A : DecProp L) →
  (a : A .fst .fst) →
  LiftDecProp {L}{L'} A .fst .fst
LiftDecPropWitness {L} {L'} (u , yes p) a = lift a
LiftDecPropWitness {L} {L'} (u , no ¬p) a = lift a

LowerDecProp'Witness :
  ∀ {L}{L'} →
  (A : DecProp' L) →
  (a : LiftDecProp' {L}{L'} A .fst) →
  A .fst
LowerDecProp'Witness {L}{L'} (u , false , v) a = lower a
LowerDecProp'Witness {L}{L'} (u , true , v) a = lower a

LowerDecPropWitness :
  ∀ {L}{L'} →
  (A : DecProp L) →
  (a : LiftDecProp {L}{L'} A .fst .fst) →
  A .fst .fst
LowerDecPropWitness {L} {L'} ((u , isProp-u) , yes p) a = lower a
LowerDecPropWitness {L} {L'} ((u , isProp-u) , no ¬p) a = lower a

LowerLiftWitness :
  ∀ {L}{L'} →
  (A : DecProp L) →
  (a : A .fst .fst) →
  LowerDecPropWitness {L}{L'} A (LiftDecPropWitness A a) ≡ a
LowerLiftWitness (_ , yes p) a = refl
LowerLiftWitness (_ , no p) a = refl

LiftLowerWitness :
  ∀ {L}{L'} →
  (A : DecProp L) →
  (a : LiftDecProp {L}{L'} A .fst .fst) →
  LiftDecPropWitness {L}{L'} A (LowerDecPropWitness {L}{L'} A a) ≡ a
LiftLowerWitness (_ , yes p) a = refl
LiftLowerWitness (_ , no p) a = refl

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

isFinSet⊤ : isFinSet ⊤
isFinSet⊤ = 1 , ∣ invEquiv ⊎-IdR-⊥-≃ ∣₁

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

_∈-FinSetDecℙ_ : ∀ {ℓ} {A : FinSet ℓ} → ⟨ A ⟩ → ⟨ FinSetDecℙ A ⟩ → Type ℓ
a ∈-FinSetDecℙ X = X a .fst .fst

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

Decℙ→Type : ∀ {ℓ} (A : FinSet ℓ) → Decℙ ⟨ A ⟩ → Type ℓ
Decℙ→Type A X = Σ[ a ∈ ⟨ A ⟩ ] ⟨ X a .fst ⟩

Decℙ'→FinSet : ∀ {ℓ} (A : FinSet ℓ) → Decℙ' (A .fst) → FinSet ℓ
fst (Decℙ'→FinSet A X) = Σ[ a ∈ ⟨ A ⟩ ] ⟨ X a ⟩
snd (Decℙ'→FinSet A X) = isFinSetSub A X

Decℙ→FinSet : ∀ {ℓ} (A : FinSet ℓ) → Decℙ ⟨ A ⟩ → FinSet ℓ
Decℙ→FinSet A X = Decℙ'→FinSet A (DecℙIso ⟨ A ⟩ .fun X)

FinSetSub :
  ∀ {ℓ ℓ'} (A : FinSet ℓ) (P : ⟨ A ⟩ → DecProp ℓ') →
  FinSet (ℓ-max ℓ ℓ')
FinSetSub A P .fst = Σ[ a ∈ ⟨ A ⟩ ] ⟨ DecProp→DecProp' (P a) ⟩
FinSetSub A P .snd = isFinSetSub A (DecProp→DecProp' ∘ P)

-- I'm pretty sure this is the `bind` of a FinSet monad
FinSetDecℙ∃ :
  ∀ {ℓ} (A B : FinSet ℓ) →
  ⟨ FinSetDecℙ A ⟩ →
  (⟨ A ⟩ → ⟨ FinSetDecℙ B ⟩) → ⟨ FinSetDecℙ B ⟩
FinSetDecℙ∃ A B ℙA f b = DecProp∃ A (λ a → DecProp× (ℙA a) (f a b))

subCardBounded :
  ∀ {ℓ ℓ'} (A : FinSet ℓ) (DecProp'B : ⟨ A ⟩ → DecProp' ℓ') →
  card (_ , isFinSetSub A DecProp'B) ≤ card A
subCardBounded A DecProp'B = card↪Inequality
  (_ , isFinSetSub A DecProp'B) A
  ∣ fst , (λ w x → isEmbeddingFstΣProp (λ a → isDecProp→isProp (str (DecProp'B a))) {w} {x}) ∣₁

-- module _
--   {ℓ ℓ'} {A : Type ℓ}
--   (isFinSetA : isFinSet A)
--   (_≺_ : A → A → Type ℓ')
--   (isDecProp≺ : (x y : A) → isDecProp (x ≺ y))
--   (isLoset≺ : IsLoset _≺_) where

--   private
--     FinSetA : FinSet ℓ
--     FinSetA = A , isFinSetA

--     _DecProp'≺_ : (x y : A) → DecProp' ℓ'
--     x DecProp'≺ y = x ≺ y , isDecProp≺ x y

--     module isLoset≺ = IsLoset isLoset≺

--     LowerFinSet : (a : A) → FinSet (ℓ-max ℓ ℓ')
--     LowerFinSet a = _ , isFinSetSub FinSetA (_DecProp'≺ a)

--     ExceptFinSet : (exception : A) → FinSet ℓ
--     ExceptFinSet exception =
--       let is-exception : A → DecProp ℓ
--           is-exception a = ((_ , isFinSet→isSet isFinSetA exception a) , isFinSet→Discrete isFinSetA exception a) in
--       _ , isFinSetSub FinSetA (DecProp→DecProp' ∘ negateDecProp ∘ is-exception)

--     exceptEquiv : (exception : A) → ⟨ ExceptFinSet exception ⟩ ⊎ ⊤ ≃ A
--     exceptEquiv exception = isoToEquiv (iso f g sec ret)
--       where
--       f : ⟨ ExceptFinSet exception ⟩ ⊎ ⊤ → A
--       f = Sum.rec fst (const exception)

--       g : A → ⟨ ExceptFinSet exception ⟩ ⊎ ⊤
--       g a = decRec (const (inr tt)) (λ ¬exception≡a → inl (a , ¬exception≡a)) (isFinSet→Discrete isFinSetA exception a)

--       sec : (a : A) → f (g a) ≡ a
--       sec a with (isFinSet→Discrete isFinSetA exception a)
--       ... | yes p = p
--       ... | no ¬p = refl

--       ret : (b : ⟨ ExceptFinSet exception ⟩ ⊎ ⊤) → g (f b) ≡ b
--       ret (inl a) with (isFinSet→Discrete isFinSetA exception (a .fst))
--       ... | yes p = ⊥.rec (a .snd p)
--       ... | no ¬p = cong inl (Σ≡Prop (λ _ → isProp¬ _) refl)
--       ret (inr tt) with (isFinSet→Discrete isFinSetA exception exception)
--       ... | yes p = refl
--       ... | no ¬p = ⊥.rec (¬p refl)

--     cardExcept : (exception : A) → suc (card (ExceptFinSet exception)) ≡ card FinSetA
--     cardExcept exception =
--       +-comm 1 (card (ExceptFinSet exception))
--       ∙ sym (card+ (ExceptFinSet exception) (⊤ , isFinSet⊤))
--       ∙ cardEquiv (_ , isFinSet⊎ (ExceptFinSet exception) (⊤ , isFinSet⊤)) FinSetA ∣ exceptEquiv exception ∣₁

--     Lower↪Except : (a : A) → ⟨ LowerFinSet a ⟩ ↪ ⟨ ExceptFinSet a ⟩
--     Lower↪Except a .fst = λ (x , x≺a) → x , λ a≡x → isLoset≺.is-irrefl _ (subst (λ a → x ≺ a) a≡x x≺a)
--     Lower↪Except a .snd = injEmbedding
--       (isFinSet→isSet (str (ExceptFinSet a)))
--       (λ p → Σ≡Prop (λ _ → isLoset≺.is-prop-valued _ _) (PathPΣ p .fst))

--     rankBounded : (a : A) → card (LowerFinSet a) < card FinSetA
--     rankBounded a = ≤<-trans
--       (card↪Inequality (LowerFinSet a) (ExceptFinSet a) ∣ Lower↪Except a ∣₁)
--       (0 , cardExcept a)

--   rank : (a : A) → Fin (card FinSetA)
--   rank a = enum (card (LowerFinSet a)) (rankBounded a)

--   rankedAt : Fin (card FinSetA) → A
--   rankedAt k = {!!}

--   rankEquiv : A ≃ Fin (card FinSetA)
--   rankEquiv = isoToEquiv (iso rank rankedAt sec ret)
--     where
--     sec : ∀ k → rank (rankedAt k) ≡ k
--     sec k = {!!}

--     ret : ∀ a → rankedAt (rank a) ≡ a
--     ret a = {!!}

--   isFinSet→isFinOrd : isFinOrd A
--   isFinSet→isFinOrd = card FinSetA , rankEquiv

SplitSupport-FinOrd : ∀ {ℓ} → {A : Type ℓ} →
  isFinOrd A → SplitSupport A
SplitSupport-FinOrd {A = A} (zero , A≃Fin) ∣a∣ =
  ⊥.rec (PT.rec isProp⊥ (A≃Fin .fst) ∣a∣)
SplitSupport-FinOrd {A = A} (suc n , A≃Fin) ∣a∣ =
  A≃Fin .snd .equiv-proof (inl _) .fst .fst

DecProp→isFinOrd :
  ∀ {ℓ} → (A : DecProp ℓ) → isFinOrd (A .fst .fst)
DecProp→isFinOrd A =
  decRec
    (λ a →
      1 ,
      isoToEquiv
      (iso
        (λ _ → inl _)
        (λ { (inl tt) → a })
        (λ { (inl tt) → refl })
        (λ a → A .fst .snd _ _)))
    (λ ¬a → 0 , uninhabEquiv ¬a (λ x → x))
    (A .snd)


isContr→isFinOrd : ∀ {ℓ} → {A : Type ℓ} →
  isContr A → isFinOrd A
isContr→isFinOrd isContrA = 1 , isContr→Equiv isContrA isContrSumFin1

DecProp'→isFinOrd :
  ∀ {ℓ} → (A : DecProp' ℓ) → isFinOrd (A .fst)
DecProp'→isFinOrd (u , true , u≃⊤) =
  EquivPresIsFinOrd
    (invEquiv u≃⊤)
    (isContr→isFinOrd isContrUnit)
DecProp'→isFinOrd (u , false , u≃⊥) =
  EquivPresIsFinOrd
    (invEquiv u≃⊥)
    isFinOrd⊥

Discrete→dec-Eq≡ :
  ∀ {ℓ} → {A : Type ℓ} →
  Discrete A →
  (a b : A) →
  Dec (a Eq.≡ b)
Discrete→dec-Eq≡ discA a b =
  decRec
    (λ a≡b → yes (Eq.pathToEq a≡b))
    (λ ¬a≡b → no (λ x → ¬a≡b (Eq.eqToPath x)))
    (discA a b)

isSet→prop-Eq≡ :
  ∀ {ℓ} → {A : Type ℓ} →
  isSet A →
  (a b : A) →
  isProp (a Eq.≡ b)
isSet→prop-Eq≡ isSetA a b Eq.refl y =
  sym (Eq.eqToPath Eq.pathToEq-reflPath) ∙
  cong (Eq.pathToEq) (isSetA a b (Eq.eqToPath Eq.refl) (Eq.eqToPath y)) ∙
  Eq.pathToEq-eqToPath y

isFinSet→DecProp-Eq≡ :
  ∀ {ℓ} → {A : Type ℓ} →
  isFinSet A →
  (a b : A) →
  DecProp ℓ
isFinSet→DecProp-Eq≡ isFinSetA a b =
  ((a Eq.≡ b) ,
  (isSet→prop-Eq≡ (isFinSet→isSet isFinSetA) a b)) ,
  Discrete→dec-Eq≡ (isFinSet→Discrete isFinSetA) a b

isFinSetFin' : ∀ {n} → isFinSet (FD.Fin n)
isFinSetFin' = isFinSetFin & subst isFinSet (sym Fin≡SumFin)
