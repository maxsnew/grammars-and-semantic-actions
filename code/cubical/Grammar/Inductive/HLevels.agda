open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.HLevels (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.W.Indexed

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet as Inductive
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX ℓY : Level

isSetValued : ∀ {X : Type ℓX} → Functor X → Type ℓX
isSetValued (k A) = isSetGrammar A
isSetValued {X = X} (Var x) = Unit*
isSetValued (&e Y F) = ∀ y → isSetValued (F y)
isSetValued (⊕e Y F) = isSet Y × (∀ y → isSetValued (F y))
isSetValued (⊗e F G) = isSetValued F × isSetValued G

module _ {X : Type ℓX} where
  FS : (F : Functor X) → String → Type ℓX
  FS F = ⟦ F ⟧ (λ x w  → Unit* {ℓX})
  opaque
    unfolding _⊗_

    FP : (F : Functor X) → (w : String) → FS F w → Type ℓX
    FP (k g) w s = ⊥*
    FP (Var x') w s = Unit*
    FP (&e Y F) w s = Σ[ y ∈ Y ] FP (F y) w (s y)
    FP (⊕e Y F) w (y , s) = FP (F y) w s
    FP (⊗e Fl Fr) _ (((wl , wr), _) , sl , sr) = FP Fl wl sl ⊎ FP Fr wr sr

    F-inX : (F : Functor X) (ix : X × String) (s : FS F (ix .snd))
      (p : FP F (ix .snd) s)
      → X × String
    F-inX (Var x) ix s p = x , (ix .snd)
    F-inX (&e Y F) ix s (y , p) = F-inX (F y) ix (s y) p
    F-inX (⊕e Y F) ix (y , s) p = F-inX (F y) ix s p
    F-inX (⊗e Fl Fr) ix (sp , sl , sr) (inl p) =
      F-inX Fl (ix .fst , sp .fst .fst) sl p
    F-inX (⊗e Fl Fr) ix (sp , sl , sr) (inr p) =
      F-inX Fr (ix .fst , sp .fst .snd) sr p

  μIW : (X → Functor X) → X × String → Type ℓX
  μIW F = IW
    (λ ix → FS (F (ix .fst)) (ix .snd))
    (λ ix → FP (F (ix .fst)) (ix .snd))
    λ ix → F-inX (F (ix .fst)) ix

  getShapeF : {A : X → Grammar ℓA}(F : Functor X)
    → ∀ w
    → ⟦ F ⟧ A w → FS F w
  getShapeF F = Inductive.map F λ x w x → tt*

  opaque
    unfolding FP _⊗_ ⊗-intro
    getSubtreeF : (A : X → Grammar ℓA) (F : Functor X)
      → ∀ w x
      → (e : ⟦ F ⟧ A w)
      → (p : FP F w (getShapeF F _ e))
      →
      let ix = (F-inX F (x , w) _ p) in
      A (ix .fst) (ix .snd)
    getSubtreeF g (Var x') w x e p = e .lower
    getSubtreeF g (&e Y F) w x e (y , p) = getSubtreeF g (F y) w x (e y) p
    getSubtreeF g (⊕e Y F) w x (y , e) p = getSubtreeF g (F y) w x e p
    getSubtreeF g (⊗e Fl Fr) w x (((wl , wr) , _) , el , er) (inl pl) =
      getSubtreeF g Fl wl x el pl
    getSubtreeF g (⊗e Fl Fr) w x (((wl , wr) , _) , el , er) (inr pr) =
      getSubtreeF g Fr wr x er pr

    nodeF : ∀ {A : X → Grammar ℓA}(F : Functor X)
      → ∀ w x
      → (s : FS F w)
      → (∀ (p : FP F w s) →
           let ix = F-inX F (x , w) s p in
           A (ix .fst) (ix .snd)
        )
      → ⟦ F ⟧ A w
    nodeF (k A) w x s subtree = lift (s .lower)
    nodeF (Var x') w x s subtree = lift (subtree tt*)
    nodeF (&e Y F) w x s subtree y =
      nodeF (F y) w x (s y) (λ p → subtree (y , p))
    nodeF (⊕e Y F) w x (y , s) subtree = y , nodeF (F y) w x s subtree
    nodeF (⊗e Fl Fr) w x (((wl , wr) , w≡wlwr) , sl , sr) subtree =
      ((wl , wr) , w≡wlwr)
        , (nodeF Fl wl x sl (λ p → subtree (inl p)))
        , ((nodeF Fr wr x sr λ p → subtree (inr p)))

    reconstructF : ∀ {A : X → Grammar ℓA}(F : Functor X)
      → ∀ w x
      → (t : ⟦ F ⟧ A w)
      → nodeF F w x (getShapeF F w t) (getSubtreeF A F w x t) ≡ t
    reconstructF (k A) w x t = refl
    reconstructF (Var y) w x t = refl
    reconstructF (&e Y F) w x t i y = reconstructF (F y) w x (t y) i
    reconstructF (⊕e Y F) w x (y , t) i = y , (reconstructF (F y) w x t i)
    reconstructF (⊗e Fl Fr) w x (((wl , wr), sp) , tl , tr) i =
      ((wl , wr) , sp) , (reconstructF Fl wl x tl i , reconstructF Fr wr x tr i)


    isSet⟦F⟧ : ∀ (F : Functor X)
      → isSetValued F
      → (A : X → SetGrammar ℓA)
      → isSetGrammar (⟦ F ⟧ (λ x → ⟨ A x ⟩))
    isSet⟦F⟧ (k _) isSetF A = isSetGrammarLift isSetF
    isSet⟦F⟧ (Var x) isSetF A = isSetGrammarLift (A x .snd)
    isSet⟦F⟧ (&e Y F) isSetF A =
      isSetGrammar&ᴰ (λ b → isSet⟦F⟧ (F b) (isSetF b) A)
    isSet⟦F⟧ (⊕e Y F) isSetF A =
      isSetGrammar⊕ᴰ (isSetF .fst) (λ b → isSet⟦F⟧ (F b) (isSetF .snd b) A)
    isSet⟦F⟧ (⊗e Fl Fr) isSetF A =
      isSetGrammar⊗ (isSet⟦F⟧ Fl (isSetF .fst) A) (isSet⟦F⟧ Fr (isSetF .snd) A)

    isSetμIW : ∀ (F : X → Functor X) → (∀ x → isSetValued (F x))
      → ∀ ix → isSet (μIW F ix)
    isSetμIW F isSetF = isOfHLevelSuc-IW 1 λ ix →
      isSet⟦F⟧ (F (ix .fst)) (isSetF (ix .fst))
        (λ x → (λ _ → Lift Unit) , λ _ → isSetUnit*)
        (ix .snd)


  {-# TERMINATING #-}
  encode : (F : X → Functor X) → ∀ ix → μ F (ix .fst) (ix .snd) → μIW F ix
  encode F (x , w) (roll .w op⟨m⟩) =
    node (Inductive.map (F x) (λ _ _ → _) w op⟨m⟩)
      λ p → encode F _ (getSubtreeF (μ F) (F x) w x _ p)

  decode : (F : X → Functor X) → ∀ ix → μIW F ix → μ F (ix .fst) (ix .snd)
  decode F (x , w) (node s subtree) =
    roll _ (nodeF (F x) w x s λ p →
      decode F (F-inX (F x) (x , w) s p) (subtree p))

  opaque
    unfolding FP _⊗_ getSubtreeF nodeF
    {-# TERMINATING #-}
    isRetract : ∀ (F : X → Functor X) x w
      → (z : μ F x w) → decode F (x , w) (encode F (x , w) z) ≡ z
    isRetract F x w (roll .w t) = cong (roll w)
      (cong (nodeF (F x) w x _) (funExt λ p → isRetract F _ _ _)
      ∙ reconstructF (F x) w x t)


isSetGrammarμ : ∀ {X : Type ℓX}
  → (F : X → Functor X)
  → (∀ x → isSetValued (F x))
  → ∀ x → isSetGrammar (μ F x)
isSetGrammarμ {X = X} F isSetValuedF x w =
  isSetRetract (encode F (x , w)) (decode F (x , w)) (isRetract F x w)
    (isSetμIW F isSetValuedF (x , w))
