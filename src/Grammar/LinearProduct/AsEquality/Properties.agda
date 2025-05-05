{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (lift ; Lift ; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

module @0 Grammar.LinearProduct.AsEquality.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Erased.Data.List
open import Erased.Lift.Base
open import Cubical.Data.List.More
import Erased.Data.Equality as Eq
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
import Grammar.Epsilon.AsEquality Alphabet isSetAlphabet as εEq
import Grammar.Epsilon.AsPath Alphabet isSetAlphabet as εPath
open import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet
import Grammar.LinearProduct.AsPath Alphabet isSetAlphabet as ⊗Path
open import Term.Base Alphabet isSetAlphabet

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
  unfolding _⊗_ ⊗Path._⊗_

  ⊗Path≡⊗Eq : (A : Grammar ℓA) (B : Grammar ℓB) → A ⊗Path.⊗ B ≡ A ⊗ B
  ⊗Path≡⊗Eq A B = funExt λ w i → Σ[ s ∈ Splitting≡SplittingEq w i ] A (s .fst .fst) × B (s .fst .snd)

  isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  isSetGrammar⊗ isSetA isSetB = subst isSetGrammar (⊗Path≡⊗Eq _ _) (⊗Path.isSetGrammar⊗ isSetA isSetB)

  ⊗-intro≡ : PathP (λ i → ⊗Path≡⊗Eq A B i ⊢ ⊗Path≡⊗Eq C D i) (f ⊗Path.,⊗ g) (f ,⊗ g)
  ⊗-intro≡ {f = f} {g = g} = funExt λ w → funExtDep λ where
    {s , a , b} {(_ , Eq.refl) , a' , b'} ⊗P≡⊗E →
      ΣPathP ((λ i → ⊗P≡⊗E i .fst) , ΣPathP ((λ i → f _ (⊗P≡⊗E i .snd .fst)) , λ i → g _ (⊗P≡⊗E i .snd .snd)))

  opaque
    unfolding εPath.ε εEq.ε ⊗Path.⊗-unit-r ⊗-unit-r
    ⊗-unit-r≡ : PathP (λ i → ⊗Path≡⊗Eq A (εEq.ε≡ i) i ⊢ A) ⊗Path.⊗-unit-r ⊗-unit-r
    ⊗-unit-r≡ {A = A} = funExt λ w → funExtDep λ where
      {s , a , eps} {(_ , Eq.refl) , a' , Eq.refl} p →
        subst A (λ i → (w≡l++r s ∙ (λ i₁ → left s ++ eps i₁) ∙ ++-unit-r (s .fst .fst)) (~ i)) a
          ≡⟨ cong (subst A _) (sym (fromPathP (λ i → p (~ i) .snd .fst)) ∙ cong (λ z → subst A z a') (isSetString _ _ _ _)) ⟩
        subst A (λ i → (w≡l++r s ∙ (λ i₁ → left s ++ eps i₁) ∙ ++-unit-r (s .fst .fst)) (~ i))
          (subst A (λ i → p (~ i) .fst .fst .fst) a')
          ≡⟨ sym (substComposite A _ _ a') ⟩
        subst A _ a'
          ≡⟨ cong (λ z → subst A z a') (isSetString _ _ _ _ ) ⟩
        subst A _ a'
          ≡⟨ sym (Eq.eqToPath (Eq.transportPathToEq→transportPath A (sym (++-unit-r _)) a')) ⟩
        Eq.transport A (Eq.pathToEq (sym (++-unit-r _))) a'
          ≡⟨ cong {x = Eq.pathToEq (sym (++-unit-r _))}
              (λ z → Eq.transport A z a') (isSetEqString _ _ _ _) ⟩
        Eq.transport A (Eq.sym (++-unit-r-Eq _)) a'
        ∎


    ⊗-unit*-r≡ : PathP (λ i → ⊗Path≡⊗Eq A (εEq.ε*≡ {ℓ = ℓ} i) i ⊢ A) ⊗Path.⊗-unit*-r ⊗-unit*-r
    ⊗-unit*-r≡ {A = A} = funExt λ w → funExtDep λ where
      {s , a , lift eps} {(_ , Eq.refl) , a' , lift Eq.refl} p →
        subst A (λ i → (w≡l++r s ∙ (λ i₁ → left s ++ eps i₁) ∙ ++-unit-r (s .fst .fst)) (~ i)) a
          ≡⟨ cong (subst A _) (sym (fromPathP (λ i → p (~ i) .snd .fst)) ∙ cong (λ z → subst A z a') (isSetString _ _ _ _)) ⟩
        subst A (λ i → (w≡l++r s ∙ (λ i₁ → left s ++ eps i₁) ∙ ++-unit-r (s .fst .fst)) (~ i))
          (subst A (λ i → p (~ i) .fst .fst .fst) a')
          ≡⟨ sym (substComposite A _ _ a') ⟩
        subst A _ a'
          ≡⟨ cong (λ z → subst A z a') (isSetString _ _ _ _ ) ⟩
        subst A _ a'
          ≡⟨ sym (Eq.eqToPath (Eq.transportPathToEq→transportPath A (sym (++-unit-r _)) a')) ⟩
        Eq.transport A (Eq.pathToEq (sym (++-unit-r _))) a'
          ≡⟨ cong {x = Eq.pathToEq (sym (++-unit-r _))}
              (λ z → Eq.transport A z a') (isSetEqString _ _ _ _) ⟩
        Eq.transport A (Eq.sym (++-unit-r-Eq _)) a'
        ∎

  opaque
    unfolding εPath.ε εEq.ε εPath.ε*-intro εEq.ε*-intro ⊗Path.⊗-unit-r⁻ ⊗-unit-r⁻
    ⊗-unit-r⁻≡ : PathP (λ i → A ⊢ ⊗Path≡⊗Eq A (εEq.ε≡ i) i) ⊗Path.⊗-unit-r⁻ ⊗-unit-r⁻
    ⊗-unit-r⁻≡ {A = A} = funExt λ w → funExt λ a →
      ΣPathP (ΣPathP (refl , isProp→PathP (isPropEq≡Path-String _ _) _ _) , ΣPathP (refl , εEq.ε-intro≡))

    ⊗-unit*-r⁻≡ : PathP (λ i → A ⊢ ⊗Path≡⊗Eq A (εEq.ε*≡ {ℓ = ℓ} i) i) ⊗Path.⊗-unit*-r⁻ ⊗-unit*-r⁻
    ⊗-unit*-r⁻≡ {A = A} = funExt λ w → funExt λ a →
      ΣPathP (ΣPathP (refl , (isProp→PathP (isPropEq≡Path-String _ _) _ _)) , ΣPathP (refl , εEq.ε*-intro≡))

  opaque
    unfolding εPath.ε εEq.ε ⊗Path.⊗-unit-l ⊗-unit-l
    ⊗-unit-l≡ : PathP (λ i → ⊗Path≡⊗Eq (εEq.ε≡ i) A i ⊢ A) ⊗Path.⊗-unit-l ⊗-unit-l
    ⊗-unit-l≡ {A = A} = funExt λ w → funExtDep λ where
      {s , eps , a} {(_ , Eq.refl) , Eq.refl , a'} p →
        subst A _ a
          ≡⟨ cong (λ z → subst A z a) (isSetString _ _ _ _) ⟩
        subst A (λ i → p i .fst .fst .snd) a
          ≡⟨ fromPathP (λ i → p i .snd .snd) ⟩
        a'
        ∎

    ⊗-unit*-l≡ : PathP (λ i → ⊗Path≡⊗Eq (εEq.ε*≡ {ℓ = ℓ} i) A i ⊢ A) ⊗Path.⊗-unit*-l ⊗-unit*-l
    ⊗-unit*-l≡ {A = A} = funExt λ w → funExtDep λ where
      {s , lift eps , a} {(_ , Eq.refl) , lift Eq.refl , a'} p →
        subst A _ a
          ≡⟨ cong (λ z → subst A z a) (isSetString _ _ _ _) ⟩
        subst A (λ i → p i .fst .fst .snd) a
          ≡⟨ fromPathP (λ i → p i .snd .snd) ⟩
        a'
        ∎

  opaque
    unfolding εPath.ε εEq.ε εPath.ε*-intro εEq.ε*-intro ⊗Path.⊗-unit-l⁻ ⊗-unit-l⁻
    ⊗-unit-l⁻≡ : PathP (λ i → A ⊢ ⊗Path≡⊗Eq (εEq.ε≡ i) A i) ⊗Path.⊗-unit-l⁻ ⊗-unit-l⁻
    ⊗-unit-l⁻≡ {A = A} = funExt λ w → funExt λ a →
      ΣPathP ((ΣPathP (refl , isProp→PathP (isPropEq≡Path-String _ _) _ _)) , (ΣPathP (εEq.ε-intro≡ , refl)))

    ⊗-unit*-l⁻≡ : PathP (λ i → A ⊢ ⊗Path≡⊗Eq (εEq.ε*≡ {ℓ = ℓ} i) A i) ⊗Path.⊗-unit*-l⁻ ⊗-unit*-l⁻
    ⊗-unit*-l⁻≡ {A = A} = funExt λ w → funExt λ a →
      ΣPathP ((ΣPathP (refl , isProp→PathP (isPropEq≡Path-String _ _) _ _)) , (ΣPathP (εEq.ε*-intro≡ , refl)))

  opaque
    unfolding ⊗Path.⊗-assoc ⊗-assoc
    ⊗-assoc≡ : PathP (λ i → ⊗Path≡⊗Eq A (⊗Path≡⊗Eq B C i) i ⊢ ⊗Path≡⊗Eq (⊗Path≡⊗Eq A B i) C i)
      ⊗Path.⊗-assoc ⊗-assoc
    ⊗-assoc≡ = funExt λ w → funExtDep λ where
      {s , (a , (s' , b , c))} {(_ , Eq.refl) , a' , ((_ , Eq.refl) , b' , c')} p →
        ΣPathP (ΣPathP (ΣPathP (
          cong₂ _++_ (λ i → p i .fst .fst .fst) (λ i → p i .snd .snd .fst .fst .fst) ,
          λ i → p i .snd .snd .fst .fst .snd) ,
          isProp→PathP (λ i → isPropEq≡Path-String _ _ i) _ _) ,
          ΣPathP (
          ΣPathP (ΣPathP (ΣPathP (
            (λ i → p i .fst .fst .fst) ,
            (λ i → p i .snd .snd .fst .fst .fst)) ,
            (isProp→PathP (λ i → isPropEq≡Path-String _ _ i) _ _)) ,
          ΣPathP ((λ i → p i .snd .fst) , (λ i → p i .snd .snd .snd .fst))) ,
          λ i → p i .snd .snd .snd .snd))

  opaque
    unfolding ⊗Path.⊗-assoc⁻ ⊗-assoc⁻
    ⊗-assoc⁻≡ : PathP (λ i → ⊗Path≡⊗Eq (⊗Path≡⊗Eq A B i) C i ⊢ ⊗Path≡⊗Eq A (⊗Path≡⊗Eq B C i) i)
      ⊗Path.⊗-assoc⁻ ⊗-assoc⁻
    ⊗-assoc⁻≡ = funExt λ w → funExtDep λ where
      {s , (s' , a , b) , c} {(_ , Eq.refl) , ((_ , Eq.refl) , a' , b') , c'} p →
        ΣPathP ((ΣPathP ((ΣPathP (
          (λ i → p i .snd .fst .fst .fst .fst) ,
          cong₂ _++_ (λ i → p i .snd .fst .fst .fst .snd) λ i → p i .fst .fst .snd)) ,
          isProp→PathP (λ i → isPropEq≡Path-String _ _ i) _ _)) ,
          (ΣPathP (
            (λ i → p i .snd .fst .snd .fst) ,
            (ΣPathP (ΣPathP (
              ΣPathP ((λ i → p i .snd .fst .fst .fst .snd) , (λ i → p i .fst .fst .snd)) ,
              (isProp→PathP (λ i → isPropEq≡Path-String _ _ i) _ _)) ,
            ΣPathP (
            (λ i → p i .snd .fst .snd .snd) ,
            λ i → p i .snd  .snd))))))
