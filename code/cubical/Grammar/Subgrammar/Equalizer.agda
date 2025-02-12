open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Grammar.Subgrammar.Equalizer (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding (k)
open import Grammar.HLevels Alphabet
open import Grammar.Subgrammar.Base Alphabet

open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    f f' f'' : g ⊢ h
    l : Grammar ℓl

module _
  {g : Grammar ℓg}
  {h : SetGrammar ℓh}
  (f f' : g ⊢ ⟨ h ⟩)
  where
  eq-prop : g ⊢ Ω
  eq-prop w x .fst = f w x ≡ f' w x
  eq-prop w x .snd = (h .snd) w (f w x) (f' w x)

  open Subgrammar eq-prop

  equalizer : Grammar (ℓ-max ℓg ℓh)
  equalizer = subgrammar

  eq-π : equalizer ⊢ g
  eq-π = sub-π

  eq-π-pf : f ∘g eq-π ≡ f' ∘g eq-π
  eq-π-pf =
    funExt λ w → funExt λ x →
    extract-pf sub-π sub-π-pf w x

  module _ (f'' : k ⊢ g) (pf' : f ∘g f'' ≡ f' ∘g f'') where
    pf : eq-prop ∘g f'' ≡ true ∘g ⊤-intro
    pf = insert-pf f'' λ w x i → pf' i w x

    eq-intro : k ⊢ equalizer
    eq-intro = sub-intro f'' pf

    eq-β : eq-π ∘g eq-intro ≡ f''
    eq-β = sub-β f'' pf

  module _ (f'' : k ⊢ equalizer) where
    eq-η : f'' ≡ eq-intro (eq-π ∘g f'') λ i → eq-π-pf i ∘g f''
    eq-η =
      sub-η f''
      ∙ cong
          (sub-intro (sub-π ∘g f''))
          (isSet⊢Ω _ _ _ _)

  equalizer-section :
    ∀ (f'' : g ⊢ equalizer) →
    (eq-π ∘g f'' ≡ id)
    → f ≡ f'
  equalizer-section f'' p =
    cong (f ∘g_) (sym p)
    ∙ cong (_∘g f'') eq-π-pf
    ∙ cong (f' ∘g_) p

module _ {A : Type ℓ} (F : A → Functor A) (g : A → SetGrammar ℓg)
  (e e' : ∀ (a : A) → μ F a ⊢ ⟨ g a ⟩)
  (pf : ∀ (a : A) →
    e  a ∘g roll ∘g map (F a) (λ a' → eq-π {h = g a'} (e a') (e' a')) ≡
    e' a ∘g roll ∘g map (F a) (λ a' → eq-π {h = g a'} (e a') (e' a'))) where

  open Subgrammar

  equalizer-ind' : ∀ (a : A) →
    eq-prop {h = g a} (e a) (e' a) ≡ true ∘g ⊤-intro
  equalizer-ind' =
    subgrammar-ind F (λ a → ⟨ g a ⟩)
      (λ a → eq-prop {h = g a} (e a) (e' a))
      (λ a →
        insert-pf (eq-prop {h = g a} (e a) (e' a))
          _
          λ w x → funExt⁻ (funExt⁻ (pf a) w) x
          )

  equalizer-ind : ∀ (a : A) → e a ≡ e' a
  equalizer-ind a =
    funExt λ w → funExt λ x →
      extract-pf
        (eq-prop {h = g a} (e a) (e' a))
        id
        (equalizer-ind' a)
        w
        x
