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

@0 isSetEqString : ∀ (w w' : String) → isProp (w Eq.≡ w')
isSetEqString _ _ = isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _)

@0 isGroupoidString : isGroupoid String
isGroupoidString = isSet→isGroupoid isSetString

NonEmptyString : Type ℓ-zero
NonEmptyString = Σ[ w ∈ String ] (w Eq.≡ [] → Empty.⊥)

record SplittingStr : Type (ℓ-suc ℓ-zero) where
  field
    Splitting : String → Type ℓ-zero
    strings : ∀ {w} → Splitting w → String × String
    @0 isSetSplitting : (w : String) → isSet (Splitting w)
    @0 SplittingPathP :
      ∀ {w : I → String}{s0 : Splitting (w i0)}{s1 : Splitting (w i1)}
      → strings s0 ≡ strings s1
      → PathP (λ i → Splitting (w i)) s0 s1
  @0 Splitting≡ : ∀ {w} → {s s' : Splitting w}
    → strings s ≡ strings s' → s ≡ s'
  Splitting≡ = SplittingPathP

open SplittingStr {{...}} public

instance
  @0 SplittingPath : SplittingStr
  SplittingPath .Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)
  SplittingPath .strings = fst
  SplittingPath .isSetSplitting w =
    isSetΣ (isSet× isSetString isSetString) λ _ → isGroupoidString _ _
  SplittingPath .SplittingPathP = ΣPathPProp (λ _ → isSetString _ _)

instance
  SplittingEq : SplittingStr
  SplittingEq .Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w Eq.≡ w₁ ++ w₂)
  SplittingEq .strings = fst
  SplittingEq .isSetSplitting w =
    isSetΣ (isSet× isSetString isSetString)
      (λ _ → isSetRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isGroupoidString _ _))
  SplittingEq .SplittingPathP =
    ΣPathPProp (λ _ → isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _))

@0 SplittingIso : ∀ w → Iso (SplittingEq .Splitting w) (SplittingPath .Splitting w)
SplittingIso w .Iso.fun s = (s .fst) , (Eq.eqToPath (s .snd))
SplittingIso w .Iso.inv s = s .fst , Eq.pathToEq (s .snd)
SplittingIso w .Iso.rightInv s i = s .fst , Eq.eqToPath-pathToEq (s .snd) i
SplittingIso w .Iso.leftInv s i = s .fst , Eq.pathToEq-eqToPath (s .snd) i

@0 Splitting→SplittingPath : ∀ w → SplittingEq .Splitting w → SplittingPath .Splitting w
Splitting→SplittingPath w = SplittingIso w .Iso.fun

@0 SplittingPath→Splitting : ∀ w → SplittingPath .Splitting w → SplittingEq .Splitting w
SplittingPath→Splitting w = SplittingIso w .Iso.inv

@0 Splitting≡SplittingPath : ∀ w → SplittingEq .Splitting w ≡ SplittingPath .Splitting w
Splitting≡SplittingPath w = isoToPath (SplittingIso w)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  DiscreteAlphabet : Discrete ⟨ Alphabet ⟩
  DiscreteAlphabet = isFinSet→Discrete isFinSetAlphabet

  DiscreteString : Discrete String
  DiscreteString = discreteList DiscreteAlphabet

-- TODO port these over to Data.Equality
-- splittingTrichotomyTy :
--   (w : String) →
--   (s s' : Splitting w) →
--   Type ℓ-zero
-- splittingTrichotomyTy w s s' =
--   ((s .fst .fst ≡ s' .fst .fst) × (s .fst .snd ≡ s' .fst .snd)) ⊎
--   (Σ[ (v , _) ∈ NonEmptyString ]
--     (Split++
--       (s .fst .fst)
--       (s .fst .snd)
--       (s' .fst .fst)
--       (s' .fst .snd)
--       v
--       ⊎
--      Split++
--       (s' .fst .fst)
--       (s' .fst .snd)
--       (s .fst .fst)
--       (s .fst .snd)
--       v
--     )
--   )

-- sameSplitting :
--   (w : String) →
--   (s s' : Splitting w) →
--   Type ℓ-zero
-- sameSplitting w s s' =
--   (s .fst .fst ≡ s' .fst .fst) × (s .fst .snd ≡ s' .fst .snd)

-- splittingPrefix :
--   (w : String) →
--   (s s' : Splitting w) →
--   Type ℓ-zero
-- splittingPrefix w s s' =
--   Σ[ (v , _) ∈ NonEmptyString ]
--     (Split++
--       (s' .fst .fst)
--       (s' .fst .snd)
--       (s .fst .fst)
--       (s .fst .snd)
--       v
--     )

-- splittingTrichotomyTy' :
--   (w : String) →
--   (s s' : Splitting w) →
--   Type ℓ-zero
-- splittingTrichotomyTy' w s s' =
--   sameSplitting w s s' ⊎
--   (
--   splittingPrefix w s' s
--     ⊎
--   splittingPrefix w s s'
--   )

-- open Iso
-- splittingTrichotomyIso :
--   (w : String) →
--   (s s' : Splitting w) →
--   Iso
--     (splittingTrichotomyTy w s s')
--     (splittingTrichotomyTy' w s s')
-- splittingTrichotomyIso w s s' =
--   ⊎Iso idIso (ΣDistR⊎Iso _ _ _)

-- isPropSplittingTrichotomyTy :
--   (w : String) →
--   (s s' : Splitting w) →
--   isProp (splittingTrichotomyTy w s s')
-- isPropSplittingTrichotomyTy w s s' =
--   isProp⊎
--     (isPropΣ (isSetString _ _) λ _ → isSetString _ _)
--     (isPropΣ⊎Split++ (Alphabet .snd) (s .fst .fst) (s .fst .snd) (s' .fst .fst) (s' .fst .snd))
--     (λ x y →
--       Sum.rec
--         (λ the-split →
--           (y .fst .snd)
--           (++unit→[] (s .fst .fst) (y .fst .fst)
--             (the-split .fst ∙ (sym (x .fst))))
--         )
--         (λ the-split →
--           (y .fst .snd)
--           (++unit→[] (s' .fst .fst) (y .fst .fst)
--             (the-split .fst ∙ (x .fst)))
--         )
--         (y .snd)
--     )

-- isPropSplittingTrichotomyTy' :
--   (w : String) →
--   (s s' : Splitting w) →
--   isProp (splittingTrichotomyTy' w s s')
-- isPropSplittingTrichotomyTy' w s s' =
--   isOfHLevelRetractFromIso
--     1
--     (invIso (splittingTrichotomyIso w s s'))
--     (isPropSplittingTrichotomyTy w s s')

-- splittingTrichotomy :
--   (w : String) →
--   (s s' : Splitting w) →
--   splittingTrichotomyTy w s s'
-- splittingTrichotomy w (([] , b) , c) (([] , e) , f) =
--   inl (refl , (sym c ∙ f))
-- splittingTrichotomy w (([] , b) , c) ((x ∷ d , e) , f) =
--   inr (((the-split .fst) ,
--     (split++NonEmpty (Alphabet .snd) [] b (x ∷ d) e
--       znots (sym c ∙ f))) , the-split .snd)
--   where
--   the-split = split++ [] b (x ∷ d) e (sym c ∙ f)
-- splittingTrichotomy w ((x ∷ a , b) , c) (([] , e) , f) =
--   inr (((the-split .fst) ,
--     (split++NonEmpty (Alphabet .snd) (x ∷ a) b [] e
--       snotz (sym c ∙ f))) , the-split .snd)
--   where
--   the-split = split++ (x ∷ a) b [] e (sym c ∙ f)
-- splittingTrichotomy [] ((x ∷ a , b) , c) ((y ∷ d , e) , f) =
--   Empty.rec (¬nil≡cons f)
-- splittingTrichotomy (w' ∷ w) ((x ∷ a , b) , c) ((y ∷ d , e) , f) =
--   Sum.rec
--     (λ (a≡d , b≡e) →
--       inl ((cong₂ _∷_ x≡y a≡d) , b≡e)
--     )
--     (λ {
--         ((v , vnotmt) , inl split) →
--           inr ((v , vnotmt) , (inl (extendSplit++ a b d e v x y x≡y split)))
--       ; ((v , vnotmt) , inr split) →
--           inr ((v , vnotmt) , (inr (extendSplit++ d e a b v y x (sym x≡y) split)))
--     })
--     recur
--   where
--   s : Splitting w
--   s .fst = a , b
--   s .snd = cons-inj₂ c
--   s' : Splitting w
--   s' .fst = d , e
--   s' .snd = cons-inj₂ f
--   x≡y : x ≡ y
--   x≡y = cons-inj₁ (sym c ∙ f)
--   recur = splittingTrichotomy w s s'

-- splittingTrichotomy' :
--   (w : String) →
--   (s s' : Splitting w) →
--   splittingTrichotomyTy' w s s'
-- splittingTrichotomy' w s s' =
--   splittingTrichotomyIso w s s' .fun (splittingTrichotomy w s s')
