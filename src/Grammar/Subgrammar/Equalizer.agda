open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Grammar.Subgrammar.Equalizer (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding
  (equalizer ; eq-π ; eq-π-pf ; eq-intro ; eq-β ; eq-η ; equalizer-section ; equalizer-ind)
open import Grammar.HLevels Alphabet using (⟨_⟩)
open import Grammar.Subgrammar.Base Alphabet

open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _
  {A : Grammar ℓA}
  {B : SetGrammar ℓB}
  (f f' : A ⊢ ⟨ B ⟩)
  where
  eq-prop : A ⊢ Ω
  eq-prop w x .fst = f w x ≡ f' w x
  eq-prop w x .snd = (B .snd) w (f w x) (f' w x)

  open Subgrammar eq-prop

  equalizer : Grammar (ℓ-max ℓA ℓB)
  equalizer = subgrammar

  eq-π : equalizer ⊢ A
  eq-π = sub-π

  eq-π-pf : f ∘g eq-π ≡ f' ∘g eq-π
  eq-π-pf =
    funExt λ w → funExt λ x →
    extract-pf sub-π sub-π-pf w x

  module _ (f'' : C ⊢ A) (pf' : f ∘g f'' ≡ f' ∘g f'') where
    pf : eq-prop ∘g f'' ≡ true ∘g ⊤-intro
    pf = insert-pf f'' λ w x i → pf' i w x

    eq-intro : C ⊢ equalizer
    eq-intro = sub-intro f'' pf

    eq-β : eq-π ∘g eq-intro ≡ f''
    eq-β = sub-β f'' pf

  module _ (f'' : C ⊢ equalizer) where
    eq-η : f'' ≡ eq-intro (eq-π ∘g f'') λ i → eq-π-pf i ∘g f''
    eq-η =
      sub-η f''
      ∙ cong
          (sub-intro (sub-π ∘g f''))
          (isSet⊢Ω _ _ _ _)

  equalizer-section :
    ∀ (f'' : A ⊢ equalizer) →
    (eq-π ∘g f'' ≡ id)
    → f ≡ f'
  equalizer-section f'' p =
    cong (f ∘g_) (sym p)
    ∙ cong (_∘g f'') eq-π-pf
    ∙ cong (f' ∘g_) p

module _ {X : Type ℓX} (F : X → Functor X) (A : X → SetGrammar ℓA)
  (e e' : ∀ (x : X) → μ F x ⊢ ⟨ A x ⟩)
  (pf : ∀ (x : X) →
    e  x ∘g roll ∘g map (F x) (λ y → eq-π {B = A y} (e y) (e' y)) ≡
    e' x ∘g roll ∘g map (F x) (λ y → eq-π {B = A y} (e y) (e' y))) where

  open Subgrammar

  equalizer-ind' : ∀ (x : X) →
    eq-prop {B = A x} (e x) (e' x) ≡ true ∘g ⊤-intro
  equalizer-ind' =
    subgrammar-ind F (λ x → ⟨ A x ⟩)
      (λ x → eq-prop {B = A x} (e x) (e' x))
      (λ x →
        insert-pf (eq-prop {B = A x} (e x) (e' x))
          _
          λ w z → funExt⁻ (funExt⁻ (pf x) w) z
          )

  equalizer-ind : ∀ (x : X) → e x ≡ e' x
  equalizer-ind x =
    funExt λ w → funExt λ z →
      extract-pf
        (eq-prop {B = A x} (e x) (e' x))
        id
        (equalizer-ind' x)
        w
        z
