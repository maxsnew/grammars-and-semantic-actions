module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq


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

module _ {ℓ : Level} {A : Type ℓ} where
  ++-unit-r-Eq : (xs : List A) → xs ++ [] Eq.≡ xs
  ++-unit-r-Eq [] = Eq.refl
  ++-unit-r-Eq (x ∷ xs) = Eq.ap (_∷_ x) (++-unit-r-Eq xs)

  module _ (isSetA : isSet A) where
    ++-unit-r-Eq≡pathToEq-++-unit-r : (xs : List A) →
      ++-unit-r-Eq xs ≡ Eq.pathToEq (++-unit-r xs)
    ++-unit-r-Eq≡pathToEq-++-unit-r xs = isPropEq _ _
      where
      isPropEq : isProp (xs ++ [] Eq.≡ xs)
      isPropEq = isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isOfHLevelList 0 isSetA _ _)

  ++-assoc-Eq : (xs ys zs : List A) → (xs ++ ys) ++ zs Eq.≡ xs ++ ys ++ zs
  ++-assoc-Eq [] ys zs = Eq.refl
  ++-assoc-Eq (x ∷ xs) ys zs = Eq.ap (_∷_ x) (++-assoc-Eq xs ys zs)

  revLength : (xs : List A) → length xs ≡ length (rev xs)
  revLength [] = refl
  revLength (x ∷ xs) =
    cong suc (revLength xs)
    ∙ cong suc (sym (+-zero (length (rev xs))))
    ∙ sym (+-suc (length (rev xs)) 0)
    ∙ sym (length++ (rev xs) ([ x ]))

  dropBack : ℕ → List A → List A
  dropBack n xs = rev (drop n (rev xs))

  dropBackLength++ :
    (xs ys : List A) →
    dropBack (length ys) (xs ++ ys) ≡ xs
  dropBackLength++ xs ys =
    cong (λ z → rev (drop (length ys) z))
      (rev-++ xs ys)
    ∙ cong (λ z → rev (drop z (rev ys ++ rev xs))) (revLength ys)
    ∙ cong rev (dropLength++ (rev ys))
    ∙ rev-rev xs

  dropBackLength : (xs : List A) → dropBack (length xs) xs ≡ []
  dropBackLength xs = dropBackLength++ [] xs

  nonEmptyList : Type ℓ
  nonEmptyList = Σ[ xs ∈ List A ] (xs ≡ [] → ⊥)

  different-lengths :
    {xs ys : List A} →
    ((length xs) ≡ (length ys) → ⊥) →
    xs ≡ ys → ⊥
  different-lengths {xs = []} {ys = []} f _ = f refl
  different-lengths {xs = []} {ys = y ∷ ys} f = ¬nil≡cons
  different-lengths {xs = x ∷ xs} {ys = []} f = ¬cons≡nil
  different-lengths {xs = x ∷ xs} {ys = y ∷ ys} f cons≡ =
    different-lengths (λ len≡ → f (cong suc len≡)) (cons-inj₂ cons≡)

  ++unit→[] :
    (xs ys : List A) →
    xs ++ ys ≡ xs →
    ys ≡ []
  ++unit→[] xs ys xs++ys≡xs =
    sym (dropLength++ xs)
    ∙ cong (drop (length xs)) xs++ys≡xs
    ∙ dropLength xs

  extendSplit++ : ∀ xs ys zs ws us x z →
    x ≡ z →
    Split++ {A = A} xs ys zs ws us →
    Split++ (x ∷ xs) ys (z ∷ zs) ws us
  extendSplit++ xs yz zs ws us x z x≡z split =
    cong₂ _∷_ x≡z (split .fst) , split .snd

  module _ (isSetA : isSet A) where
    isPropSplit++ : ∀ xs ys zs ws us →
      isProp (Split++ xs ys zs ws us)
    isPropSplit++ xs ys zs ws us a b =
      ΣPathP (
        (isOfHLevelList 0 isSetA (xs ++ us) zs (fst a) (fst b)) ,
        (isOfHLevelList 0 isSetA ys (us ++ ws) (snd a) (snd b))
      )

    isPropΣSplit++ : ∀ xs ys zs ws →
      isProp (Σ[ us ∈ List A ] Split++ xs ys zs ws us)
    isPropΣSplit++ xs ys zs ws a b =
      Σ≡Prop
        (λ us → isPropSplit++ xs ys zs ws us)
        (
        sym (dropLength++ xs)
        ∙ cong (drop (length xs)) (a .snd .fst ∙ (sym (b .snd .fst)))
        ∙ dropLength++ xs
        )

    isPropΣ⊎Split++ : ∀ xs ys zs ws →
      isProp (
        Σ[ (us , _) ∈ nonEmptyList ]
          (Split++ xs ys zs ws us
            ⊎
          Split++ zs ws xs ys us)
      )
    isPropΣ⊎Split++ xs ys zs ws a b =
      Σ≡Prop
        (λ (us , not-mt) →
          isProp⊎
            (isPropSplit++ xs ys zs ws us)
            (isPropSplit++ zs ws xs ys us)
            (λ s s' →
              not-mt
              (
              sym (dropLength++ us)
              ∙ cong (drop (length us))
                (sym (dropLength++ xs)
                ∙ cong (drop (length xs))
                  (sym (++-assoc xs us us)
                    ∙ cong (_++ us) (s .fst) ∙ (s' .fst))
                ∙ dropLength xs)
              ∙ drop[] (length us)
              )
            )
        )
        (Σ≡Prop
          (λ _ → isProp→ isProp⊥)
          (Sum.rec
            (λ aL →
              Sum.rec
                (λ bL → cong fst (isPropΣSplit++ xs ys zs ws (_ , aL) (_ , bL)))
                (λ bR →
                  Empty.rec
                    (
                    a .fst .snd
                      (sym (dropLength++ (b .fst .fst))
                      ∙ cong (drop (length (b .fst .fst)))
                      (++unit→[] zs (b .fst .fst ++ a .fst .fst)
                        (sym (++-assoc zs (b .fst .fst) (a .fst .fst))
                        ∙ cong (_++ a .fst .fst) (bR .fst)
                        ∙ aL .fst))
                      ∙ drop[] (length (b .fst .fst)))
                    )
                )
                (b .snd)
            )
            (λ aR →
              Sum.rec
                (λ bL →
                    (
                    Empty.rec
                    ( b .fst .snd
                      (sym (dropLength++ (a .fst .fst))
                      ∙ cong (drop (length (a .fst .fst)))
                      (++unit→[] zs (a .fst .fst ++ b .fst .fst)
                        (sym (++-assoc zs (a .fst .fst) (b .fst .fst))
                        ∙ cong (_++ b .fst .fst) (aR .fst)
                        ∙ bL .fst))
                      ∙ drop[] (length (a .fst .fst))) )
                    )
                )
                (λ bR → cong fst (isPropΣSplit++ zs ws xs ys (_ , aR) (_ , bR)))
                (b .snd)
            )
            (a .snd)
          )
        )

    split++NonEmpty : ∀ (xs ys zs ws : List A) →
      (length xs ≡ length zs → Empty.⊥) →
      (p : xs ++ ys ≡ zs ++ ws) →
      split++ xs ys zs ws p .fst ≡ [] →
      ⊥
    split++NonEmpty xs ys zs ws len p split-mt =
      Sum.rec
        (λ s → len (
        cong length
          (sym (++-unit-r xs) ∙ (cong (xs ++_) (sym split-mt)) ∙ (s .fst))
        ))
        (λ s →
          len (
            cong length
            (sym (s .fst) ∙ (cong (zs ++_) (split-mt)) ∙ ++-unit-r zs))
        )
        (the-split .snd)
      where the-split = split++ xs ys zs ws p
