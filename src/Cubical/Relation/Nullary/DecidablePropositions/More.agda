module Cubical.Relation.Nullary.DecidablePropositions.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.Empty as ⊥
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Sum as Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.FinSet.Properties

private
  variable
    ℓ ℓ' : Level

negateDecProp : ∀ {ℓ} → DecProp ℓ → DecProp ℓ
fst (fst (negateDecProp A)) = ¬ A .fst .fst
snd (fst (negateDecProp A)) = isProp→ isProp⊥
snd (negateDecProp A) =
  decRec
    (λ a → no (λ x → x a))
    (λ ¬a → yes ¬a)
    (A .snd)

¬DecProp_ : ∀ {ℓ} → DecProp ℓ → DecProp ℓ
¬DecProp_ = negateDecProp

⟨_⟩DecProp : ∀ {ℓ} → (A : DecProp ℓ) → Type ℓ
⟨ A ⟩DecProp = A .fst .fst

DecProp⊥* : ∀ {ℓ} → DecProp ℓ
DecProp⊥* = (⊥* , isProp⊥*) , no lower

doubleNegDecProp' :
  ∀ {ℓ} (A : DecProp ℓ) →
  negateDecProp (negateDecProp A) .fst .fst →
  A .fst .fst
doubleNegDecProp' A x = Dec→Stable (A .snd) x

¬¬elimDecProp :
  ∀ {ℓ} (A : DecProp ℓ) →
  negateDecProp (negateDecProp A) .fst .fst →
  A .fst .fst
¬¬elimDecProp A a  = doubleNegDecProp' A a

DecLift :
  {A : Type ℓ} →
  Dec A → Dec (Lift ℓ' A)
DecLift {L} {L'} {A} (yes p) = yes (lift p)
DecLift {L} {L'} {A} (no ¬p) = no (λ x → ¬p (lower x))

discreteLift :
  {A : Type ℓ}
  (ℓ' : Level)
  → Discrete A → Discrete (Lift ℓ' A)
discreteLift ℓ' discreteA x y =
  decRec
    (λ lx≡ly → yes (liftExt lx≡ly))
    (λ lx≢ly → no (λ p → lx≢ly (cong lower p)))
    (discreteA (lower x) (lower y))

open Iso
DecPropIso : ∀ {ℓ} → Iso (DecProp ℓ) (DecProp' ℓ)
DecPropIso .fun (A , dec) = ⟨ A ⟩ , decRec
  (λ a → true , isContr→Equiv (a , λ y → str A _ _) isContrUnit)
  (λ ¬a → false , uninhabEquiv ¬a (λ x → x))
  dec
DecPropIso .inv (A , isDecPropA) =
  (A , isDecProp→isProp isDecPropA) , isDecProp→Dec isDecPropA
DecPropIso .sec (a , false , c) =
  ΣPathP (refl , (ΣPathP (refl ,
    isPropCod→isProp≃ isProp⊥ _ c )))
DecPropIso .sec (a , true , c) =
  ΣPathP (refl , (ΣPathP (refl ,
    isPropCod→isProp≃ isPropUnit _ c)))
DecPropIso .ret (A , yes p) =
  Σ≡Prop (λ x → isPropDec (x .snd))
    (ΣPathP (refl , (isPropIsProp _ _)))
DecPropIso .ret (A , no ¬p) =
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

DecProp× :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : DecProp ℓ) →
  DecProp ℓ
DecProp× A B = DecPropΣ A (λ _ → B)

DecProp'× :
  ∀ {ℓ} → (A : DecProp' ℓ) → (B : DecProp' ℓ) → DecProp' ℓ
DecProp'× A B = (A .fst × B .fst) , (isDecProp× A B)

DecProp≡ : ∀ {ℓ} {A : Type ℓ} → Discrete A → A → A → DecProp ℓ
DecProp≡ disc x y = ((x ≡ y) , Discrete→isSet disc x y) , disc x y

Bool-iso-DecProp' : ∀ {ℓ} → Iso Bool (DecProp' ℓ)
Bool-iso-DecProp' .fun false .fst = ⊥*
Bool-iso-DecProp' .fun false .snd .fst = false
Bool-iso-DecProp' .fun false .snd .snd = uninhabEquiv lower (λ x → x)
Bool-iso-DecProp' .fun true .fst = Unit*
Bool-iso-DecProp' .fun true .snd .fst = true
Bool-iso-DecProp' .fun true .snd .snd = isContr→Equiv isContrUnit* isContrUnit
Bool-iso-DecProp' .inv (a , false , c) = false
Bool-iso-DecProp' .inv (a , true , c) = true
Bool-iso-DecProp' .sec (a , false , c) =
  ΣPathP
    (sym (ua (compEquiv c ⊥≃⊥*)) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y →
          Σ≡Prop isPropIsEquiv (isProp→ isProp⊥ _ _)) _ _)))
  where
  ⊥≃⊥* : ⊥ ≃ ⊥*
  ⊥≃⊥* = uninhabEquiv (λ x → x) lower
Bool-iso-DecProp' .sec (a , true , c) =
  ΣPathP
    ((sym (ua (compEquiv c Unit≃Unit*))) ,
      (ΣPathP
        (refl ,
        isProp→PathP (λ i → λ x y →
          Σ≡Prop isPropIsEquiv (isProp→ isPropUnit _ _)) _ _)))
Bool-iso-DecProp' .ret false = refl
Bool-iso-DecProp' .ret true = refl

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

DecProp→Bool : ∀ {ℓ} → DecProp ℓ → Bool
DecProp→Bool (_ , yes p) = true
DecProp→Bool (_ , no ¬p) = false

isFinSetDecProp : ∀ {ℓ} → isFinSet (DecProp ℓ)
fst isFinSetDecProp = 2
snd isFinSetDecProp = ∣ the-equiv ∣₁
  where
  the-equiv : DecProp ℓ ≃ Fin 2
  the-equiv = compEquiv (invEquiv Bool≃DecProp) (invEquiv SumFin2≃Bool)

LiftDecProp'' :
  ∀ {L}{L'} →
  DecProp L →
  DecProp (ℓ-max L L')
LiftDecProp'' {L} {L'} (p , _) .fst .fst = Lift L' (p .fst)
LiftDecProp'' {L} {L'} (p , _) .fst .snd = isPropLift (p .snd)
LiftDecProp'' (p , yes yep) .snd = yes (lift yep)
LiftDecProp'' (p , no nope) .snd = no (λ lyep → nope (lyep .lower))

LiftDecProp :
  ∀ {L}{L'} →
  DecProp L →
  DecProp (ℓ-max L L')
LiftDecProp {L} {L'} (a , yes p) =
  ((Lift L' (a .fst)) , (isPropLift (a .snd))) , (yes (lift p))
LiftDecProp {L} {L'} (a , no ¬p) =
  ((Lift L' (a .fst)) , (isPropLift (a .snd))) , (no λ x → ¬p (lower x))

LiftDecProp' :
  ∀ {L}{L'} →
  DecProp' L →
  DecProp' (ℓ-max L L')
LiftDecProp' {L} {L'} (a , false , c) =
  (Lift L' a) , (false , (compEquiv (invEquiv LiftEquiv) c))
LiftDecProp' {L} {L'} (a , true , c) =
  (Lift L' a) , (true , (compEquiv (invEquiv LiftEquiv) c))

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

FinSetSub :
  ∀ {ℓ ℓ'} (A : FinSet ℓ) (P : ⟨ A ⟩ → DecProp ℓ') →
  FinSet (ℓ-max ℓ ℓ')
FinSetSub A P .fst = Σ[ a ∈ ⟨ A ⟩ ] ⟨ DecProp→DecProp' (P a) ⟩
FinSetSub A P .snd = isFinSetSub A (DecProp→DecProp' ∘ P)

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

SplitSupport-FinOrd : ∀ {ℓ} → {A : Type ℓ} →
  isFinOrd A → SplitSupport A
SplitSupport-FinOrd {A = A} (zero , A≃Fin) ∣a∣ =
  ⊥.rec (PT.rec isProp⊥ (A≃Fin .fst) ∣a∣)
SplitSupport-FinOrd {A = A} (suc n , A≃Fin) ∣a∣ =
  A≃Fin .snd .equiv-proof (inl _) .fst .fst

witness-true :
  (A : DecProp' ℓ) → A .fst →
  true Eq.≡ Bool-iso-DecProp' .inv A
witness-true {ℓ} (ty , true , _) a = Eq.refl
witness-true {ℓ} (ty , false , snd₁) a = ⊥.rec (snd₁ .fst a)

truth→witness :
  ∀ {ℓ} →
  (b : Bool) → true Eq.≡ b →
  fun (Bool-iso-DecProp' {ℓ = ℓ}) b .fst
truth→witness true true≡b = lift tt
