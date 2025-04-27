open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module String.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.List.More
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.More
open import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Data.Sigma

String : Type ℓ-zero
String = List ⟨ Alphabet ⟩

@0 isSetString : isSet String
isSetString = isOfHLevelList 0 (str Alphabet)

-- @0 isSetEqString : ∀ (w w' : String) → isProp (w Eq.≡ w')
-- isSetEqString _ _ = isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _)

@0 isGroupoidString : isGroupoid String
isGroupoidString = isSet→isGroupoid isSetString

NonEmptyString : Type ℓ-zero
NonEmptyString = Σ[ w ∈ String ] (w ≡ [] → Empty.⊥)

@0 Splitting : String → Type ℓ-zero
Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

@0 left right : ∀ {w} → Splitting w → String
left s = s .fst .fst
right s = s .fst .snd

@0 w≡l++r : ∀ {w} → (s : Splitting w) → w ≡ left s ++ right s
w≡l++r s = s .snd

SplittingEq : String → Type ℓ-zero
SplittingEq w = Σ[ (w₁ , w₂) ∈ String × String ] (w Eq.≡ w₁ ++ w₂)

leftEq rightEq : ∀ {w} → SplittingEq w → String
leftEq s = s .fst .fst
rightEq s = s .fst .snd

@0 Splitting≡SplittingEq : ∀ w → Splitting w ≡ SplittingEq w
Splitting≡SplittingEq w i = Σ[ (w₁ , w₂) ∈ String × String ] Eq.PathPathEq {x = w} {y = w₁ ++ w₂} i

@0 isSetSplitting : (w : String) → isSet (Splitting w)
isSetSplitting w = isSetΣ (isSet× isSetString isSetString) λ _ → isGroupoidString _ _

@0 isSetSplittingEq : (w : String) → isSet (SplittingEq w)
isSetSplittingEq w = subst isSet (Splitting≡SplittingEq w) (isSetSplitting w)

@0 SplittingPathP : ∀ {w : I → String}{s0 : Splitting (w i0)}{s1 : Splitting (w i1)}
  → s0 .fst ≡ s1 .fst → PathP (λ i → Splitting (w i)) s0 s1
SplittingPathP = ΣPathPProp λ _ → isSetString _ _

@0 Splitting≡ : ∀ {w} → {s s' : Splitting w} → s .fst ≡ s' .fst → s ≡ s'
Splitting≡ = SplittingPathP

-- @0 SplittingEqPathP : ∀ {w : I → String}{s0 : SplittingEq (w i0)}{s1 : SplittingEq (w i1)}
--   → s0 .fst ≡ s1 .fst → PathP (λ i → SplittingEq (w i)) s0 s1
-- SplittingEqPathP s≡ = {!!}


module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  DiscreteAlphabet : Discrete ⟨ Alphabet ⟩
  DiscreteAlphabet = isFinSet→Discrete isFinSetAlphabet

  DiscreteString : Discrete String
  DiscreteString = discreteList DiscreteAlphabet

module _ (c : ⟨ Alphabet ⟩) where
  splitChar : (w : String) → Splitting (c ∷ w)
  splitChar w = ([ c ] , w) , refl

splitting++ : ∀ w1 w2 → Splitting (w1 ++ w2)
splitting++ w1 w2 = ((w1 , w2) , refl)

splittingTrichotomyTy :
  (w : String) →
  (s s' : Splitting w) →
  Type ℓ-zero
splittingTrichotomyTy w s s' =
  ((s .fst .fst ≡ s' .fst .fst) × (s .fst .snd ≡ s' .fst .snd)) ⊎
  (Σ[ (v , _) ∈ NonEmptyString ]
    (Split++
      (s .fst .fst)
      (s .fst .snd)
      (s' .fst .fst)
      (s' .fst .snd)
      v
      ⊎
     Split++
      (s' .fst .fst)
      (s' .fst .snd)
      (s .fst .fst)
      (s .fst .snd)
      v
    )
  )

sameSplitting :
  (w : String) →
  (s s' : Splitting w) →
  Type ℓ-zero
sameSplitting w s s' =
  (s .fst .fst ≡ s' .fst .fst) × (s .fst .snd ≡ s' .fst .snd)

splittingPrefix :
  (w : String) →
  (s s' : Splitting w) →
  Type ℓ-zero
splittingPrefix w s s' =
  Σ[ (v , _) ∈ NonEmptyString ]
    (Split++
      (s' .fst .fst)
      (s' .fst .snd)
      (s .fst .fst)
      (s .fst .snd)
      v
    )

splittingTrichotomyTy' :
  (w : String) →
  (s s' : Splitting w) →
  Type ℓ-zero
splittingTrichotomyTy' w s s' =
  sameSplitting w s s' ⊎
  (
  splittingPrefix w s' s
    ⊎
  splittingPrefix w s s'
  )

open Iso
splittingTrichotomyIso :
  (w : String) →
  (s s' : Splitting w) →
  Iso
    (splittingTrichotomyTy w s s')
    (splittingTrichotomyTy' w s s')
splittingTrichotomyIso w s s' =
  ⊎Iso idIso (ΣDistR⊎Iso _ _ _)

@0 isPropSplittingTrichotomyTy : (w : String) → (s s' : Splitting w) → isProp (splittingTrichotomyTy w s s')
isPropSplittingTrichotomyTy w s s' =
  isProp⊎
    (isPropΣ (isSetString _ _) λ _ → isSetString _ _)
    (isPropΣ⊎Split++ (Alphabet .snd) (s .fst .fst) (s .fst .snd) (s' .fst .fst) (s' .fst .snd))
    (λ x y →
      Sum.rec
        (λ the-split →
          (y .fst .snd)
          (++unit→[] (s .fst .fst) (y .fst .fst)
            (the-split .fst ∙ (sym (x .fst))))
        )
        (λ the-split →
          (y .fst .snd)
          (++unit→[] (s' .fst .fst) (y .fst .fst)
            (the-split .fst ∙ (x .fst)))
        )
        (y .snd)
    )

@0 isPropSplittingTrichotomyTy' : (w : String) → (s s' : Splitting w) → isProp (splittingTrichotomyTy' w s s')
isPropSplittingTrichotomyTy' w s s' =
  isOfHLevelRetractFromIso
    1
    (invIso (splittingTrichotomyIso w s s'))
    (isPropSplittingTrichotomyTy w s s')

splittingTrichotomy : (w : String) → (s s' : Splitting w) → splittingTrichotomyTy w s s'
splittingTrichotomy w (([] , b) , c) (([] , e) , f) =
  inl (refl , (sym c ∙ f))
splittingTrichotomy w (([] , b) , c) ((x ∷ d , e) , f) =
  inr (((the-split .fst) ,
    (split++NonEmpty (Alphabet .snd) [] b (x ∷ d) e
      znots (sym c ∙ f))) , the-split .snd)
  where
  the-split = split++ [] b (x ∷ d) e (sym c ∙ f)
splittingTrichotomy w ((x ∷ a , b) , c) (([] , e) , f) =
  inr (((the-split .fst) ,
    (split++NonEmpty (Alphabet .snd) (x ∷ a) b [] e
      snotz (sym c ∙ f))) , the-split .snd)
  where
  the-split = split++ (x ∷ a) b [] e (sym c ∙ f)
splittingTrichotomy [] ((x ∷ a , b) , c) ((y ∷ d , e) , f) =
  Empty.rec (¬nil≡cons f)
splittingTrichotomy (w' ∷ w) ((x ∷ a , b) , c) ((y ∷ d , e) , f) =
  Sum.rec
    (λ (a≡d , b≡e) →
      inl ((cong₂ _∷_ x≡y a≡d) , b≡e)
    )
    (λ {
        ((v , vnotmt) , inl split) →
          inr ((v , vnotmt) , (inl (extendSplit++ a b d e v x y x≡y split)))
      ; ((v , vnotmt) , inr split) →
          inr ((v , vnotmt) , (inr (extendSplit++ d e a b v y x (sym x≡y) split)))
    })
    recur
  where
  s : Splitting w
  s .fst = a , b
  s .snd = cons-inj₂ c
  s' : Splitting w
  s' .fst = d , e
  s' .snd = cons-inj₂ f
  x≡y : x ≡ y
  x≡y = cons-inj₁ (sym c ∙ f)
  recur = splittingTrichotomy w s s'

splittingTrichotomy' :
  (w : String) →
  (s s' : Splitting w) →
  splittingTrichotomyTy' w s s'
splittingTrichotomy' w s s' =
  splittingTrichotomyIso w s s' .fun (splittingTrichotomy w s s')
