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
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
import Cubical.Data.Fin as Fin
import Cubical.Data.Fin.Arithmetic as Arith
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

DecProp≃DecProp' : ∀ {ℓ} → DecProp ℓ ≃ DecProp' ℓ
DecProp≃DecProp' = isoToEquiv DecPropIso

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

-- DecSubset : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
-- DecSubset {ℓ} A =
--   Σ[ X ∈ Type ℓ ] Σ[ f ∈ (X ↪ A) ] Σ[ P ∈ Decℙ A ]
--     (∀ (x : X) → P (f .fst x) .fst .fst)

-- DecSubset-subsingleton :

-- List→DecSubset :
--   ∀ {ℓ} → (A : Type ℓ) → List A → DecSubset A
-- List→DecSubset A [] =
--   ⊥* ,
--   (((λ x → ⊥.rec (lower x)) ,
--   λ w x → record { equiv-proof = λ y → ⊥.rec (lower x) }) ,
--   (λ x → (⊥* , (λ x₁ y → ⊥.rec (lower y))) , no (λ x₁ → lower x₁)) ,
--   (λ x → ⊥.rec (lower x)))
-- List→DecSubset A (x ∷ L) = {!!}



-- TODO decidable powerset
--
-- fromℕ< : (m n : ℕ) → m Ord.< n → Fin n
-- fromℕ< zero (suc n) _ = fzero
-- fromℕ< (suc m) (suc n) p = fsuc (fromℕ< m n p )

-- FinSetℙ : ∀ {ℓ} → FinSet ℓ → FinSet (ℓ-suc ℓ)
-- fst (FinSetℙ A) = Decℙ (A .fst)
-- snd (FinSetℙ A) =
--   Cubical.HITs.PropositionalTruncation.rec
--     isPropIsFinSet
--     (λ A≃Fin → (2 ^ A .snd .fst) ,
--       ∣ the-equiv A≃Fin ∣₁)
--     (A .snd .snd)
--     where

--     -- Bitvector : (n : ℕ) → Type
--     -- Bitvector n = Fin.FinVec Bool n

--     -- bv-iso :
--     --   A .fst ≃ Fin (A .snd .fst) →
--     --   Iso (Decℙ (A .fst)) (Bitvector (A .snd .fst))
--     -- fun (bv-iso x) S m =
--     --   decRec
--     --     (λ _ → true)
--     --     (λ _ → false)
--     --     (S the-a .snd)
--     --   where
--     --   the-a = x .snd .equiv-proof (Fin→SumFin m) .fst .fst
--     -- inv (bv-iso x) v a =
--     --   Cubical.Data.Bool.elim
--     --     (DecPropIso .inv (Unit* ,
--     --       (true , (isContr→Equiv isContrUnit* isContrUnit))))
--     --     (DecPropIso .inv (⊥* ,
--     --       (false , uninhabEquiv (λ x → lower x) λ x → x)))
--     --     (v (SumFin→Fin (x .fst a)))
--     -- rightInv (bv-iso x) b = {!refl!}
--     -- leftInv (bv-iso x) a = {!!}


--     -- help : ∀ {m} → (n : ℕ) → n Ord.< m → (Fin m → DecProp ℓ) → ℕ
--     -- help {m = m} zero p S = decRec (λ _ → 1) (λ _ → 0) (S (fromℕ< 0 m p) .snd)
--     -- help {m = m} (suc n) p S =
--     --   decRec
--     --     (λ _ → (2 ^ (suc n)) + help n a S)
--     --     (λ _ → help n a S)
--     --     (S (fromℕ< (suc n) m p) .snd)
--     --   where
--     --   a = Ord.<-weaken {suc n}{m} p

--     -- the-iso :
--     --   0 Ord.< A .snd .fst →
--     --   A .fst ≃ Fin (A .snd .fst) →
--     --   Iso (Decℙ (A .fst)) (Fin (2 ^ A .snd .fst))
--     -- fun (the-iso p x) S =
--     --   fromℕ< (help {m = A .snd .fst} (predℕ (A .snd .fst)) (pred< (A .snd .fst) p)
--     --     λ a → S (x .snd .equiv-proof a .fst .fst)) (2 ^ A .snd .fst) {!!}
--     --   where
--     --   pred< : (n : ℕ) → 0 Ord.< n → predℕ n Ord.< n
--     --   pred< (suc n) x = Ord.≤-refl n

--     --   caseDec : ∀ {ℓ ℓ' ℓ''} {P : Type ℓ} {A : Type ℓ'}(B : A → Type ℓ'') → (ifyes : P → A) →
--     --     (ifno : ¬ P → A) →
--     --     ((p : P) → B (ifyes p)) →
--     --     ((¬p : ¬ P) → B (ifno ¬p)) →
--     --     (d : Dec P) →
--     --       B (decRec ifyes ifno d)
--     --   caseDec B ifyes ifno fy fn (yes p) = fy p
--     --   caseDec B ifyes ifno fy fn (no ¬p) = fn ¬p

--     --   lem : (n : ℕ) → (x : 0 Ord.< n) → (S : Fin n → DecProp ℓ) →
--     --    help (predℕ n) (pred< n x) S Ord.< (2 ^ n)
--     --   lem (suc zero) _ S =
--     --     caseDec
--     --       (λ a → a Ord.< 2)
--     --       ((λ _ → 1))
--     --       (λ _ → 0)
--     --       (λ _ → tt)
--     --       (λ _  → tt)
--     --       (S (fromℕ< 0 1 (pred< 1 _)) .snd)
--     --   lem (suc (suc n)) x S =
--     --     -- {!!}
--     --     caseDec
--     --       (λ a → a Ord.< (2 ^ n) + ((2 ^ n) + zero) + ((2 ^ n) + ((2 ^ n) + zero) + zero))
--     --       (λ _ →
--     --         (2 ^ n) + ((2 ^ n) + zero) +
--     --         help n (Ord.<-weaken n (Ord.≤-refl n) S) S)
--     --       (λ _ → help n (Ord.<-weaken n (Ord.≤-refl n) S) S)
--     --       (λ p → {!!})
--     --       (λ ¬p → {!!} )
--     --       (S (fsuc (fromℕ< n (suc n) (Ord.≤-refl n))) .snd)

--     -- inv (the-iso p x) = {!!}
--     -- rightInv (the-iso p x) = {!!}
--     -- leftInv (the-iso p x) = {!!}

--     the-equiv :
--       A .fst ≃ Fin (A .snd .fst) →
--       Decℙ (A .fst) ≃ Fin (2 ^ A .snd .fst)
--     fst (the-equiv x) f =
--       SumFinℙ≃ (A .snd .fst) .fst
--         (fst ∘ snd ∘ (DecPropIso .fun) ∘ f ∘ equivToIso x .inv)
--     fst (fst (equiv-proof (snd (the-equiv x)) y)) a =
--       {!equivToIso (SumFinℙ≃ (A .snd .fst)) .inv ?!}
--     snd (fst (equiv-proof (snd (the-equiv x)) y)) = {!!}
--     snd (equiv-proof (snd (the-equiv x)) y) fib = {!!}
