open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Properties (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List hiding (rec)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Grammar Alphabet hiding (k)
open import Grammar.SequentialUnambiguity.Base Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Grammar.SequentialUnambiguity.FollowLast Alphabet
open import Grammar.External.HLevels.Properties Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

open StrongEquivalence

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (seq-unambig : A ⊛ B)
  where
  opaque
    unfolding the-split _⊗_ ⊗-intro _&_ literal
    ⊛→unique-splitting :
      (w : String) →
      (p : (A ⊗ B) w) →
      (q : (A ⊗ B) w) →
      same-splits {w = λ _ → w} p q
    ⊛→unique-splitting w (ps , pA , pB) (qs , qA , qB) =
      Sum.rec
        (λ sameSplit → ΣPathP (sameSplit .fst , sameSplit .snd))
        (Sum.rec
          (λ {
              (([] , notmt) , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _) , ps11++cw'≡qs11 , ps12≡cw'++qs12) →
              Sum.rec
                (λ c∉FLA →
                  Empty.rec
                    (get⊥
                      (c∉FLA (qs .fst .fst)
                        ((((ps .fst .fst , c ∷ w') ,
                            Eq.pathToEq (sym ps11++cw'≡qs11)) ,
                          (pA ,
                            (((c ∷ [] , w') , Eq.refl) ,
                              (lit-intro ,
                                (string-intro {A = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) ,
                          qA))))
                (λ c∉FB →
                  Empty.rec
                    (get⊥
                      (c∉FB (ps .fst .snd)
                        ((((c ∷ [] , w' ++ qs .fst .snd) ,
                            Eq.pathToEq ps12≡cw'++qs12) ,
                          (lit-intro ,
                            (string-intro {A = ⌈ w' ++ qs .fst .snd ⌉})
                              (w' ++ qs .fst .snd)
                              (mk⌈⌉ (w' ++ qs .fst .snd)))) ,
                          pB))))
                (seq-unambig c)
          })
          (λ {
              (([] , notmt) , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _) , qs11++cw'≡ps11 , qs12≡cw'++ps12) →
              Sum.rec
                (λ c∉FLA →
                  Empty.rec
                    (get⊥
                      (c∉FLA (ps .fst .fst)
                        ((((qs .fst .fst , c ∷ w') ,
                            Eq.pathToEq (sym qs11++cw'≡ps11)) ,
                          (qA ,
                            (((c ∷ [] , w') , Eq.refl) ,
                              (lit-intro ,
                                (string-intro {A = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) ,
                          pA))))
                (λ c∉FB →
                  Empty.rec
                    (get⊥
                      (c∉FB (qs .fst .snd)
                        ((((c ∷ [] , w' ++ ps .fst .snd) ,
                            Eq.pathToEq qs12≡cw'++ps12) ,
                          (lit-intro ,
                            (string-intro {A = ⌈ w' ++ ps .fst .snd ⌉})
                              (w' ++ ps .fst .snd)
                              (mk⌈⌉ (w' ++ ps .fst .snd)))) ,
                          qB))))
                (seq-unambig c)
          })
        )
        (splittingTrichotomy' w (splittingEq→Path ps) (splittingEq→Path qs))

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (unambig-A : unambiguous A)
  (unambig-B : unambiguous B)
  (seq-unambig : A ⊛ B)
  where
  opaque
    unfolding _&_ ⊗-intro the-split _⊗_
    private
      isLang-⊗ : isLang (A ⊗ B)
      isLang-⊗ w x y =
        Σ≡Prop
          (λ s →
            isProp×
              (unambiguous→isLang unambig-A (s .fst .fst))
              (unambiguous→isLang unambig-B (s .fst .snd)))
          s≡
        where
        s≡ : x .fst ≡ y .fst
        s≡ = SplittingEq≡ (⊛→unique-splitting seq-unambig w x y)

    unambiguous-⊗ : unambiguous (A ⊗ B)
    unambiguous-⊗ = isLang→unambiguous isLang-⊗
