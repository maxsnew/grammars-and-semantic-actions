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
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

isSetValued : ∀ {A : Type ℓ} → Functor A → Type ℓ
isSetValued (k g) = isSetGrammar g
isSetValued {A = A} (Var a) = Unit*
isSetValued (&e B F) = ∀ b → isSetValued (F b)
isSetValued (⊕e B F) = isSet B × (∀ b → isSetValued (F b))
isSetValued (⊗e F G) = isSetValued F × isSetValued G

module _ {A : Type ℓ} where
  FS : (F : Functor A) → String → Type ℓ
  FS F = ⟦ F ⟧ (λ a w  → Unit* {ℓ})
  opaque
    unfolding _⊗_

    FP : (F : Functor A) → (w : String) → FS F w → Type ℓ
    FP (k g) w s = ⊥*
    FP (Var a') w s = Unit*
    FP (&e B F) w s = Σ[ b ∈ B ] FP (F b) w (s b)
    FP (⊕e B F) w (b , s) = FP (F b) w s
    FP (⊗e Fl Fr) _ (((wl , wr), _) , sl , sr) = FP Fl wl sl ⊎ FP Fr wr sr

    F-inX : (F : Functor A) (ix : A × String) (s : FS F (ix .snd))
      (p : FP F (ix .snd) s)
      → A × String
    F-inX (Var a) ix s p = a , (ix .snd)
    F-inX (&e B F) ix s (b , p) = F-inX (F b) ix (s b) p
    F-inX (⊕e B F) ix (b , s) p = F-inX (F b) ix s p
    F-inX (⊗e Fl Fr) ix (sp , sl , sr) (inl p) =
      F-inX Fl (ix .fst , sp .fst .fst) sl p
    F-inX (⊗e Fl Fr) ix (sp , sl , sr) (inr p) =
      F-inX Fr (ix .fst , sp .fst .snd) sr p

  μIW : (A → Functor A) → A × String → Type ℓ
  μIW F = IW
    (λ ix → FS (F (ix .fst)) (ix .snd))
    (λ ix → FP (F (ix .fst)) (ix .snd))
    λ ix → F-inX (F (ix .fst)) ix

  getShapeF : {g : A → Grammar ℓ'}(F : Functor A)
    → ∀ w
    → ⟦ F ⟧ g w → FS F w
  getShapeF F = Inductive.map F λ a w x → tt*

  opaque
    unfolding FP _⊗_ ⊗-intro
    getSubtreeF : (g : A → Grammar ℓ') (F : Functor A)
      → ∀ w a
      → (e : ⟦ F ⟧ g w)
      → (p : FP F w (getShapeF F _ e))
      →
      let ix = (F-inX F (a , w) _ p) in
      g (ix .fst) (ix .snd)
    getSubtreeF g (Var a') w a e p = e .lower
    getSubtreeF g (&e B F) w a e (b , p) = getSubtreeF g (F b) w a (e b) p
    getSubtreeF g (⊕e B F) w a (b , e) p = getSubtreeF g (F b) w a e p
    getSubtreeF g (⊗e Fl Fr) w a (((wl , wr) , _) , el , er) (inl pl) =
      getSubtreeF g Fl wl a el pl
    getSubtreeF g (⊗e Fl Fr) w a (((wl , wr) , _) , el , er) (inr pr) =
      getSubtreeF g Fr wr a er pr

    nodeF : ∀ {g : A → Grammar ℓ'}(F : Functor A)
      → ∀ w a
      → (s : FS F w)
      → (∀ (p : FP F w s) →
           let ix = F-inX F (a , w) s p in
           g (ix .fst) (ix .snd)
        )
      → ⟦ F ⟧ g w
    nodeF (k g) w a s subtree = lift (s .lower)
    nodeF (Var a') w a s subtree = lift (subtree tt*)
    nodeF (&e B F) w a s subtree b =
      nodeF (F b) w a (s b) (λ p → subtree (b , p))
    nodeF (⊕e B F) w a (b , s) subtree = b , nodeF (F b) w a s subtree
    nodeF (⊗e Fl Fr) w a (((wl , wr) , w≡wlwr) , sl , sr) subtree =
      ((wl , wr) , w≡wlwr)
        , (nodeF Fl wl a sl (λ p → subtree (inl p)))
        , ((nodeF Fr wr a sr λ p → subtree (inr p)))

    reconstructF : ∀ {g : A → Grammar ℓ'}(F : Functor A)
      → ∀ w a
      → (t : ⟦ F ⟧ g w)
      → nodeF F w a (getShapeF F w t) (getSubtreeF g F w a t) ≡ t
    reconstructF (k g) w a t = refl
    reconstructF (Var a') w a t = refl
    reconstructF (&e B F) w a t i b = reconstructF (F b) w a (t b) i
    reconstructF (⊕e B F) w a (b , t) i = b , (reconstructF (F b) w a t i)
    reconstructF (⊗e Fl Fr) w a (((wl , wr), sp) , tl , tr) i =
      ((wl , wr) , sp) , (reconstructF Fl wl a tl i , reconstructF Fr wr a tr i)


    isSet⟦F⟧ : ∀ (F : Functor A)
      → isSetValued F
      → (g : A → SetGrammar ℓ')
      → isSetGrammar (⟦ F ⟧ (λ a → ⟨ g a ⟩))
    isSet⟦F⟧ (k _) isSetF g = isSetGrammarLift isSetF
    isSet⟦F⟧ (Var a) isSetF g = isSetGrammarLift (g a .snd)
    isSet⟦F⟧ (&e B F) isSetF g =
      isSetGrammar&ᴰ (λ b → isSet⟦F⟧ (F b) (isSetF b) g)
    isSet⟦F⟧ (⊕e B F) isSetF g =
      isSetGrammar⊕ᴰ (isSetF .fst) (λ b → isSet⟦F⟧ (F b) (isSetF .snd b) g)
    isSet⟦F⟧ (⊗e Fl Fr) isSetF g =
      isSetGrammar⊗ (isSet⟦F⟧ Fl (isSetF .fst) g) (isSet⟦F⟧ Fr (isSetF .snd) g)

    isSetμIW : ∀ (F : A → Functor A) → (∀ a → isSetValued (F a))
      → ∀ ix → isSet (μIW F ix)
    isSetμIW F isSetF = isOfHLevelSuc-IW 1 λ ix →
      isSet⟦F⟧ (F (ix .fst)) (isSetF (ix .fst))
        (λ x → (λ _ → Lift Unit) , λ _ → isSetUnit*)
        (ix .snd)


  {-# TERMINATING #-}
  encode : (F : A → Functor A) → ∀ ix → μ F (ix .fst) (ix .snd) → μIW F ix
  encode F (a , w) (roll .w op⟨m⟩) =
    node (Inductive.map (F a) (λ _ _ → _) w op⟨m⟩)
      λ p → encode F _ (getSubtreeF (μ F) (F a) w a _ p)

  decode : (F : A → Functor A) → ∀ ix → μIW F ix → μ F (ix .fst) (ix .snd)
  decode F (a , w) (node s subtree) =
    roll _ (nodeF (F a) w a s λ p →
      decode F (F-inX (F a) (a , w) s p) (subtree p))

  opaque
    unfolding FP _⊗_ getSubtreeF nodeF
    {-# TERMINATING #-}
    isRetract : ∀ (F : A → Functor A) a w
      → (x : μ F a w) → decode F (a , w) (encode F (a , w) x) ≡ x
    isRetract F a w (roll .w t) = cong (roll w)
      (cong (nodeF (F a) w a _) (funExt λ p → isRetract F _ _ _)
      ∙ reconstructF (F a) w a t)


isSetGrammarμ : ∀ {A : Type ℓ}
  → (F : A → Functor A)
  → (∀ a → isSetValued (F a))
  → ∀ a → isSetGrammar (μ F a)
isSetGrammarμ {A = A} F isSetValuedF a w =
  isSetRetract (encode F (a , w)) (decode F (a , w)) (isRetract F a w)
    (isSetμIW F isSetValuedF (a , w))

