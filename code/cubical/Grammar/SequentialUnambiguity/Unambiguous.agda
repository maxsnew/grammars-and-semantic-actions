{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Unambiguous (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Empty as Empty

-- open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
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
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    c : ⟨ Alphabet ⟩

open isStrongEquivalence
open StrongEquivalence

private
  module
    _
    {g : Grammar ℓg}
    {h : Grammar ℓh}
    (seq-unambig : g ⊛ h)
    where
    opaque
      unfolding the-split _⊗_ ⊗-intro _&_ literal
      ⊛→unique-splitting :
        (w : String) →
        (p : (g ⊗ h) w) →
        (q : (g ⊗ h) w) →
        same-splits {w = λ _ → w} p q
      ⊛→unique-splitting w (ps , pg , ph) (qs , qg , qh) =
        Sum.rec
          (λ sameSplit → ΣPathP ((sameSplit .fst) , (sameSplit .snd)))
          (Sum.rec
            (λ {
              (([] , notmt ), _ , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _ ), ps11++cw'≡qs11 , ps12≡cw'++qs12) →
              Sum.rec
                (λ c∉FLg →
                  Empty.rec (
                    get⊥
                      (c∉FLg (qs .fst .fst)
                      (((_ , (sym ps11++cw'≡qs11)) ,
                        (pg , ((([ c ] , w') , refl) , (lit-intro  , (string-intro {g = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) , qg)
                    )
                  )
                )
                (λ c∉Fh →
                  Empty.rec (
                    get⊥
                      (c∉Fh (ps .fst .snd)
                        (((_ , ps12≡cw'++qs12) ,
                          (lit-intro , ((
                            string-intro {g = ⌈ w' ++ qs .fst .snd ⌉})
                              (w' ++ qs .fst .snd) (mk⌈⌉ (w' ++ qs .fst .snd))))) , ph)
                    )
                  )
                )
                (seq-unambig c)
              })
            (λ {
              (([] , notmt ), _ , _) → Empty.rec (notmt refl)
            ; ((c ∷ w' , _ ), qs11++cw'≡ps11 , qs12≡cw'++ps12) →
              Sum.rec
                (λ c∉FLg →
                  Empty.rec (
                    get⊥
                      (c∉FLg (ps .fst .fst)
                      (((_ , (sym qs11++cw'≡ps11)) ,
                        (qg , ((([ c ] , w') , refl) , (lit-intro  , (string-intro {g = ⌈ w' ⌉}) w' (mk⌈⌉ w'))))) , pg)
                    )
                  )
                )
                (λ c∉Fh →
                  Empty.rec (
                    get⊥
                      (c∉Fh (qs .fst .snd)
                        (((_ , qs12≡cw'++ps12) ,
                          (lit-intro , ((
                            string-intro {g = ⌈ w' ++ ps .fst .snd ⌉})
                              (w' ++ ps .fst .snd) (mk⌈⌉ (w' ++ ps .fst .snd))))) , qh)
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
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig : g ⊛ h)
  (unambig-g : unambiguous g)
  (unambig-h : unambiguous h)
  where

  opaque
    unfolding &-intro ⊗-intro the-split
    private
      isLang⊗ : isLang (g ⊗ h)
      isLang⊗ w x y =
        Σ≡Prop
          (λ s →
            isProp×
              (EXTERNAL.unambiguous→isLang unambig-g (s .fst .fst))
              (EXTERNAL.unambiguous→isLang unambig-h (s .fst .snd))
          )
          s≡
        where
        s≡ : x .fst ≡ y .fst
        s≡ = Splitting≡ (⊛→unique-splitting seq-unambig w x y)

    unambiguous-⊗ : unambiguous (g ⊗ h)
    unambiguous-⊗ = EXTERNAL.isLang→unambiguous isLang⊗

module
  _
  {g : Grammar ℓg}
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig : g ⊛ g)
  (unambig-g : unambiguous g)
  where

  unambiguous-* : unambiguous (g *)
  unambiguous-* = {!!}
