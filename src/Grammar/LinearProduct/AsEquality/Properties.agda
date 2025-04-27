open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

module @0 Grammar.LinearProduct.AsEquality.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
import Grammar.Epsilon.AsEquality Alphabet as εEq
import Grammar.Epsilon.AsPath Alphabet as εPath
import Grammar.LinearProduct.AsEquality.Base Alphabet as ⊗Eq
import Grammar.LinearProduct.AsPath Alphabet as ⊗Path
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
    g : C ⊢ D

opaque
  unfolding ⊗Eq._⊗_ ⊗Path._⊗_

  ⊗Path≡⊗Eq : A ⊗Path.⊗ B ≡ A ⊗Eq.⊗ B
  ⊗Path≡⊗Eq {A = A} {B = B} =
    funExt λ w i →
      Σ[ s ∈ Splitting≡SplittingEq w i ] A (s .fst .fst) × B (s .fst .snd)

  isSetGrammar⊗Eq : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗Eq.⊗ B)
  isSetGrammar⊗Eq isSetA isSetB = subst isSetGrammar ⊗Path≡⊗Eq (⊗Path.isSetGrammar⊗ isSetA isSetB)

  opaque
    unfolding ⊗Eq.⊗-intro ⊗Path.⊗-intro
    ⊗-intro≡ :
        PathP (λ i → ⊗Path≡⊗Eq {A = A} {B = B} i ⊢ ⊗Path≡⊗Eq {A = C} {B = D} i) (f ⊗Path.,⊗ g) (f ⊗Eq.,⊗ g)
    ⊗-intro≡ {f = f} {g = g} = funExt λ w → funExtDep (λ where
        {⊗P} {⊗Eq} ⊗P≡⊗Eq →
            ΣPathP (
            (λ i → ⊗P≡⊗Eq i .fst) ,
            ΣPathP (
                (λ i → f (⊗P≡⊗Eq i .fst .fst .fst) (⊗P≡⊗Eq i .snd .fst)) ,
                (λ i → g (⊗P≡⊗Eq i .fst .fst .snd) (⊗P≡⊗Eq i .snd .snd)))))
  opaque
    unfolding ⊗Eq.⊗-unit-r ⊗Path.⊗-unit-r εEq.ε εPath.ε
    ⊗-unit-r≡ :
        PathP (λ i → ⊗Path≡⊗Eq {A = A} {B = εEq.ε≡ i} i ⊢ A) ⊗Path.⊗-unit-r ⊗Eq.⊗-unit-r
    ⊗-unit-r≡ {A = A} = funExt λ w → funExtDep (λ where
      {(s , aPath , eps)} {(((w' , _) , Eq.refl) , aEq , Eq.refl)} ⊗P≡⊗Eq →
        subst A (sym (w≡l++r s ∙ cong (left s ++_) eps ∙ ++-unit-r (left s))) aPath
          ≡⟨ (λ i →
               subst A
                (sym (w≡l++r s ∙ cong (left s ++_) eps ∙ ++-unit-r (left s)))
                (fromPathP (λ j → ⊗P≡⊗Eq (~ j) .snd .fst) (~ i) )) ⟩
        subst A _ (subst A (λ j → ⊗P≡⊗Eq (~ j) .fst .fst .fst) aEq)
          ≡⟨ sym (substComposite A _ _ aEq) ⟩
        subst A _ aEq
          ≡⟨ (λ i → subst A (isSetString _ _
            ((λ j →
              ⊗P≡⊗Eq (~ j) .fst .fst .fst) ∙
              sym (w≡l++r s ∙ cong (left s ++_) eps ∙ ++-unit-r (left s)))
            (sym (++-unit-r _)) i) aEq) ⟩
        subst A (sym (++-unit-r _)) aEq
          ≡⟨ sym (Eq.eqToPath
            (Eq.transportPathToEq→transportPath A (sym (++-unit-r _)) aEq)) ⟩
        Eq.transport A (Eq.pathToEq (sym (++-unit-r _))) aEq
          ≡⟨ ((λ i → Eq.transport A
            (isSetEqString _ _
              (Eq.pathToEq (sym (++-unit-r _)))
              (Eq.sym (++-unit-r-Eq _)) i) aEq)) ⟩
        Eq.transport A (Eq.sym (++-unit-r-Eq _)) aEq
        ∎)
