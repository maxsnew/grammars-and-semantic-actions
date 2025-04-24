open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
  hiding (Splitting
        ; isSetSplitting
        ; SplittingPathP
        ; Splitting≡)
  renaming (SplittingEq to Splitting
          ; isSetSplittingEq to isSetSplitting)
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsEquality Alphabet
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
  (A ⊗ B) w = Σ[ s ∈ Splitting w ] A (s .fst .fst) × B (s .fst .snd)

  -- @0 isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  -- isSetGrammar⊗ isSetG isSetB w = isSetΣ (isSetSplitting w)
  --   λ _ → isSet× (isSetG _) (isSetB _)

infixr 25 _⊗_

opaque
  unfolding _⊗_
  ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
  ⊗-intro e e' _ (s , a , c) = s , e _ a , e' _ c

_,⊗_ = ⊗-intro
infixr 20 _,⊗_

opaque
  unfolding _⊗_ ⊗-intro
  opaque
    unfolding ε
    ⊗-unit-r : A ⊗ ε ⊢ A
    ⊗-unit-r {A = A} w ((_ , Eq.refl) , a , Eq.refl) =
      Eq.transport A (Eq.sym (++-unit-r-Eq _)) a

    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
    ⊗-unit-r⁻ w p = ((w , []) , Eq.sym (++-unit-r-Eq w)) , p , ε-intro

    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l {A = A} _ ((_ , Eq.refl) , Eq.refl , a) = a

    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    ⊗-unit-l⁻ _ p = (_ , Eq.refl) , ε-intro , p

  ⊗-assoc :
    A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
  ⊗-assoc _ (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) =
    ((wa ++ wb , wc) , Eq.sym (++-assoc-Eq wa wb wc)) , ((((wa , wb) , Eq.refl) , (a , b)) , c)

  ⊗-assoc⁻ :
    (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
  ⊗-assoc⁻ _ (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) =
    ((wa , wb ++ wc) , ++-assoc-Eq wa wb wc) , (a , (((wb , wc) , Eq.refl) , (b , c)))

{- ε* versions of the unitors  -}
⊗-unit*-l : ε* {ℓ} ⊗ A ⊢ A
⊗-unit*-l = ⊗-unit-l ∘g ⊗-intro lowerG id

⊗-unit*-l⁻ : A ⊢ ε* {ℓ} ⊗ A
⊗-unit*-l⁻ = ⊗-intro liftG id ∘g ⊗-unit-l⁻

⊗-unit*-r : A ⊗ ε* {ℓ} ⊢ A
⊗-unit*-r = ⊗-unit-r ∘g ⊗-intro id lowerG

⊗-unit*-r⁻ : A ⊢ A ⊗ ε* {ℓ}
⊗-unit*-r⁻ = ⊗-intro id liftG ∘g ⊗-unit-r⁻

-- {- Big associators and big diagrams -}

⊗-assoc⁻3 : (A ⊗ B ⊗ C) ⊗ D ⊢ A ⊗ B ⊗ C ⊗ D
⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

⊗-assoc3 : A ⊗ B ⊗ C ⊗ D ⊢ (A ⊗ B ⊗ C) ⊗ D
⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

⊗-assoc⁻4 : (A ⊗ B ⊗ C ⊗ D) ⊗ E ⊢ A ⊗ B ⊗ C ⊗ D ⊗ E
⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

⊗-assoc4 : A ⊗ B ⊗ C ⊗ D ⊗ E ⊢ (A ⊗ B ⊗ C ⊗ D) ⊗ E
⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3
