{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Unambiguous (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Grammar Alphabet hiding (k)
open import Grammar.String.Properties Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.LinearProduct.SplittingTrichotomy Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Grammar.SequentialUnambiguity.FollowLast Alphabet
open import Grammar.SequentialUnambiguity.Base Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB
    c : ⟨ Alphabet ⟩

open isStrongEquivalence
open StrongEquivalence

-- All of the below is a proof in the semantics, so don't use it
private
  module
    _
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
          (λ sameSplit → ΣPathP ((sameSplit .fst) , (sameSplit .snd)))
          (Sum.rec
            (λ {
              (([] , notmt ), _ , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _ ), ps11++cw'≡qs11 , ps12≡cw'++qs12) →
              Sum.rec
                (λ c∉FLA →
                  Empty.rec (
                    get⊥
                      (c∉FLA (qs .fst .fst)
                      (((_ , (sym ps11++cw'≡qs11)) ,
                        (pA , ((([ c ] , w') , refl) , (lit-intro  , (string-intro {A = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) , qA)
                    )
                  )
                )
                (λ c∉FB →
                  Empty.rec (
                    get⊥
                      (c∉FB (ps .fst .snd)
                        (((_ , ps12≡cw'++qs12) ,
                          (lit-intro , ((
                            string-intro {A = ⌈ w' ++ qs .fst .snd ⌉})
                              (w' ++ qs .fst .snd) (mk⌈⌉ (w' ++ qs .fst .snd))))) , pB)
                    )
                  )
                )
                (seq-unambig c)
              })
            (λ {
              (([] , notmt ), _ , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _ ), qs11++cw'≡ps11 , qs12≡cw'++ps12) →
              Sum.rec
                (λ c∉FLA →
                  Empty.rec (
                    get⊥
                      (c∉FLA (ps .fst .fst)
                      (((_ , (sym qs11++cw'≡ps11)) ,
                        (qA , ((([ c ] , w') , refl) , (lit-intro  , (string-intro {A = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) , pA)
                    )
                  )
                )
                (λ c∉FB →
                  Empty.rec (
                    get⊥
                      (c∉FB (qs .fst .snd)
                        (((_ , qs12≡cw'++ps12) ,
                          (lit-intro , ((
                            string-intro {A = ⌈ w' ++ ps .fst .snd ⌉})
                              (w' ++ ps .fst .snd) (mk⌈⌉ (w' ++ ps .fst .snd))))) , qB)
                    )
                  )
                )
                (seq-unambig c)
              })
          )
          (splittingTrichotomy' w ps qs)
        where
        w≡ : ps .fst .fst ++ ps .fst .snd ≡ qs .fst .fst ++ qs .fst .snd
        w≡ = sym (ps .snd) ∙ qs .snd


module
  _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (¬nullA : ⟨ ¬Nullable A ⟩)
  (seq-unambig : A ⊛ B)
  (unambig-A : unambiguous A)
  (unambig-B : unambiguous B)
  where

  -- TODO ideally this proof would happen internally rather than appealing
  -- to the fact that this forms a language
  opaque
    unfolding &-intro ⊗-intro the-split
    private
      isLang⊗ : isLang (A ⊗ B)
      isLang⊗ w x y =
        Σ≡Prop
          (λ s →
            isProp×
              (EXTERNAL.unambiguous→isLang unambig-A (s .fst .fst))
              (EXTERNAL.unambiguous→isLang unambig-B (s .fst .snd))
          )
          s≡
        where
        s≡ : x .fst ≡ y .fst
        s≡ = Splitting≡ (⊛→unique-splitting seq-unambig w x y)

    unambiguous-⊗ : unambiguous (A ⊗ B)
    unambiguous-⊗ = EXTERNAL.isLang→unambiguous isLang⊗

module
  _
  {A : Grammar ℓA}
  (¬nullA : ⟨ ¬Nullable A ⟩)
  (seq-unambig : A ⊛ A)
  (unambig-A : unambiguous A)
  where

  unambiguous-* : unambiguous (A *)
  unambiguous-* = {!!}
