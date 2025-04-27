open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.LinearProduct.AsPath.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsPath Alphabet
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
    f f' f'' f''' f'''' f''''' : A ⊢ B

opaque
  _⊗_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⊗ B) w = Σ[ s ∈ Splitting w ] A (left s) × B (right s)

  ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
  ⊗-intro e f _ (s , a , c) = s , e _ a , f _ c

opaque
  unfolding ε _⊗_
  ⊗-unit-l : ε ⊗ A ⊢ A
  ⊗-unit-l {A = A} _ (s , eps , a) =
    subst A (sym (w≡l++r s ∙ cong (_++ right s) eps)) a

  ⊗-unit-l⁻ : A ⊢ ε ⊗ A
  ⊗-unit-l⁻ _ a = splitting++ [] _ , ε-intro , a

opaque
  unfolding ε _⊗_
  ⊗-unit-r : A ⊗ ε ⊢ A
  ⊗-unit-r {A = A} w (s , a , eps) =
    subst A (sym (w≡l++r s ∙ cong (left s ++_) eps ∙ ++-unit-r _)) a

  ⊗-unit-r⁻ : A ⊢ A ⊗ ε
  ⊗-unit-r⁻ _ a = (_ , (sym (++-unit-r _))) , a , ε-intro

opaque
  unfolding _⊗_
  ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
  ⊗-assoc _ (s , a , (s' , b , c)) =
    (_ , w≡l++r s ∙ cong (left s ++_) (w≡l++r s') ∙ sym (++-assoc (left s) (left s') (right s'))) ,
      (splitting++ _ _ , a , b) , c

  ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
  ⊗-assoc⁻ _ (s , (s' , a , b) , c) =
    (_ , w≡l++r s ∙ cong (_++ right s) (w≡l++r s') ∙ ++-assoc (left s') (right s') (right s)) ,
      a , (splitting++ (right s') (right s) , b , c)

infixr 25 _⊗_

_,⊗_ = ⊗-intro
infixr 20 _,⊗_

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

open StrongEquivalence
module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  {C : Grammar ℓC} {D : Grammar ℓD}
  (A≅B : A ≅ B) (C≅D : C ≅ D)
  where

  private
    the-fun : A ⊗ C ⊢ B ⊗ D
    the-fun = A≅B .fun ,⊗ C≅D .fun

    the-inv : B ⊗ D ⊢ A ⊗ C
    the-inv = A≅B .inv ,⊗ C≅D .inv
    opaque
      unfolding ⊗-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec i = A≅B .sec i ,⊗ C≅D .sec i

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret i = A≅B .ret i ,⊗ C≅D .ret i

  ⊗≅ : (A ⊗ C) ≅ (B ⊗ D)
  ⊗≅ .fun = the-fun
  ⊗≅ .inv = the-inv
  ⊗≅ .sec = the-sec
  ⊗≅ .ret = the-ret
