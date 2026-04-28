open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
  hiding (Splitting
        ; isSetSplitting
        ; SplittingPathP
        ; Splitting≡
        ; splitting++)
  renaming (SplittingEq to Splitting
          ; isSetSplittingEq to isSetSplitting
          ; SplittingEqPathP to SplittingPathP
          ; SplittingEq≡ to Splitting≡
          ; leftEq to left
          ; rightEq to right
          ; splittingEq++ to splitting++)
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsEquality.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓG
      ℓH ℓK ℓL ℓM ℓN ℓO
      ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    E : Grammar ℓE
    F : Grammar ℓF
    G : Grammar ℓG
    H : Grammar ℓH
    K : Grammar ℓK
    L : Grammar ℓL
    M : Grammar ℓM
    N : Grammar ℓN
    O : Grammar ℓO

opaque
  _⊗_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⊗ B) w = Σ[ s ∈ Splitting w ] A (left s) × B (right s)

  ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
  ⊗-intro e e' _ (s , a , c) = s , e _ a , e' _ c

  ⊗-mk : ∀ {w} (s : Splitting w) → A (left s) → B (right s) → (A ⊗ B) w
  ⊗-mk s a b = s , a , b

infixr 25 _⊗_

_,⊗_ = ⊗-intro
infixr 20 _,⊗_

opaque
  unfolding _⊗_ ⊗-intro
  opaque
    unfolding ε
    ⊗-unit-r : A ⊗ ε ⊢ A
    ⊗-unit-r {A = A} w (((w' , w'') , e) , a , e') =
      Eq.transport A
        (Eq.sym (++-unit-r-Eq w')
          Eq.∙ Eq.ap (w' ++_) (Eq.sym e')
          Eq.∙ Eq.sym e)
        a

    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
    ⊗-unit-r⁻ w p =
      ((w , []) , Eq.sym (++-unit-r-Eq w)) , p , ε-intro

    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l {A = A} w (((w' , w'') , e) , e' , a) =
      Eq.transport A (Eq.sym (Eq.ap (_++ w'') e') Eq.∙ Eq.sym e) a

    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    ⊗-unit-l⁻ _ p = (_ , Eq.refl) , ε-intro , p

  ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
  ⊗-assoc {A = A}{B = B}{C = C} w
    (((wa , wbc) , e) , a , (((wb , wc) , e') , b , c)) =
    ((wa ++ wb , wc)
      , e Eq.∙ Eq.ap (wa ++_) e' Eq.∙ Eq.sym (++-assoc-Eq wa wb wc))
      , ((((wa , wb) , Eq.refl) , (a , b)) , c)

  ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
  ⊗-assoc⁻ {A = A}{B = B}{C = C} w
    (((wab , wc) , e) , (((wa , wb) , e') , a , b) , c) =
    ((wa , wb ++ wc)
      , e Eq.∙ Eq.ap (_++ wc) e' Eq.∙ ++-assoc-Eq wa wb wc)
      , (a , (((wb , wc) , Eq.refl) , (b , c)))

{- ε* versions of the unitors -}
⊗-unit*-l : ε* {ℓ} ⊗ A ⊢ A
⊗-unit*-l = ⊗-unit-l ∘g ⊗-intro lowerG id

⊗-unit*-l⁻ : A ⊢ ε* {ℓ} ⊗ A
⊗-unit*-l⁻ = ⊗-intro liftG id ∘g ⊗-unit-l⁻

⊗-unit*-r : A ⊗ ε* {ℓ} ⊢ A
⊗-unit*-r = ⊗-unit-r ∘g ⊗-intro id lowerG

⊗-unit*-r⁻ : A ⊢ A ⊗ ε* {ℓ}
⊗-unit*-r⁻ = ⊗-intro id liftG ∘g ⊗-unit-r⁻

{- Big associators -}
⊗-assoc⁻3 : (A ⊗ B ⊗ C) ⊗ D ⊢ A ⊗ B ⊗ C ⊗ D
⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

⊗-assoc3 : A ⊗ B ⊗ C ⊗ D ⊢ (A ⊗ B ⊗ C) ⊗ D
⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

⊗-assoc⁻4 : (A ⊗ B ⊗ C ⊗ D) ⊗ E ⊢ A ⊗ B ⊗ C ⊗ D ⊗ E
⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

⊗-assoc4 : A ⊗ B ⊗ C ⊗ D ⊗ E ⊢ (A ⊗ B ⊗ C ⊗ D) ⊗ E
⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3
