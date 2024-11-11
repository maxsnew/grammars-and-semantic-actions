{- The initial algebra of a strictly positive functor, constructed as an IW type -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.IW (Alphabet : hSet ℓ-zero)where

open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec; map)
open import Cubical.Data.Unit
open import Cubical.Data.W.Indexed

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.StrictlyPositiveFunctor Alphabet as SPF hiding (map)
open import Term.Base Alphabet

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

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

    F-inX : (F : Functor A) (w : String) (s : FS F w)
      (p : FP F w s)
      → A × String
    F-inX (Var a) w s p = a , w
    F-inX (&e B F) w s (b , p) = F-inX (F b) w (s b) p
    F-inX (⊕e B F) w (b , s) p = F-inX (F b) w s p
    F-inX (⊗e Fl Fr) _ (sp , sl , sr) (inl p) =
      F-inX Fl (sp .fst .fst) sl p
    F-inX (⊗e Fl Fr) _ (sp , sl , sr) (inr p) =
      F-inX Fr (sp .fst .snd) sr p

  Container : (F : Functor A) → (A → Grammar ℓ') → Grammar (ℓ-max ℓ ℓ')
  Container F g w = Σ[ s ∈ FS F w ]
    (∀ (p : FP F w s) →
         let ix = F-inX F w s p in
         g (ix .fst) (ix .snd))

  map : ∀ (F : Functor A) {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}
      → (∀ a → g a ⊢ h a)
      → Container F g ⊢ Container F h
  map F f w (s , child) = s , (λ p → f _ _ (child p))

  -- containerHomo : ∀ (F : A → Functor A){g : A → Grammar ℓ'}{h : A → Grammar ℓ''} → Algebra F g → Algebra F h → Type _
  -- containerHomo F {g = g}{h} α β = Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ] (∀ a → {!α!})

  module _ {g : A → Grammar ℓ'} where
    getShapeF : {g : A → Grammar ℓ'}(F : Functor A)
      → ∀ w
      → ⟦ F ⟧ g w → FS F w
    getShapeF F = SPF.map F λ a w x → tt*

    opaque
      unfolding FP _⊗_ ⊗-intro
      getSubtreeF : (F : Functor A)
        → ∀ w
        → (e : ⟦ F ⟧ g w)
        → (p : FP F w (getShapeF F _ e))
        → let ix = (F-inX F w _ p) in g (ix .fst) (ix .snd)
      getSubtreeF (Var a') w e p = e .lower
      getSubtreeF (&e B F) w e (b , p) = getSubtreeF (F b) w (e b) p
      getSubtreeF (⊕e B F) w (b , e) p = getSubtreeF (F b) w e p
      getSubtreeF (⊗e Fl Fr) w (((wl , wr) , _) , el , er) (inl pl) =
        getSubtreeF Fl wl el pl
      getSubtreeF (⊗e Fl Fr) w (((wl , wr) , _) , el , er) (inr pr) =
        getSubtreeF Fr wr er pr

      toContainer : (F : Functor A)
       → ⟦ F ⟧ g ⊢ Container F g
      toContainer F w t = (getShapeF F w t) , getSubtreeF F w t

      fromContainer : ∀ (F : Functor A) → Container F g ⊢ ⟦ F ⟧ g
      fromContainer (k g) _ (s , child) = lift (s .lower)
      fromContainer (Var a) _ (s , child) = lift (child tt*)
      fromContainer (&e B F) _ (s , child) b = fromContainer (F b) _ (s b , (λ p → child (b , p)))
      fromContainer (⊕e B F) _ ((b , s) , child) = b , (fromContainer (F b) _ (s , child))
      fromContainer (⊗e Fl Fr) _ ((splits , sl , sr) , child) =
       splits
        , (fromContainer Fl _ (sl , λ p → child (inl p)))
        , (fromContainer Fr _ (sr , λ p → child (inr p)))
      open StrongEquivalence

      secFC : ∀ (F : Functor A) w t → (fromContainer F ∘g toContainer F) w t ≡ t
      secFC (k g) w t = refl
      secFC (Var a) w t = refl
      secFC (&e B F) w t i b = secFC (F b) w (t b) i
      secFC (⊕e B F) w (b , t) i = b , secFC (F b) w t i
      secFC (⊗e Fl Fr) w (splits , tl , tr) i = splits , (secFC Fl _ tl i , secFC Fr _ tr i)

      retFC1 : ∀ (F : Functor A) w t →
        (toContainer F ∘g fromContainer F) w t .fst ≡ t .fst
      retFC1 (Var a) w t = refl
      retFC1 (k g) w t = refl
      retFC1 (&e B F) w (s , child) = funExt λ b →
        retFC1 (F b) w (s b , (λ p → child (b , p)))
      retFC1 (⊕e B F) w ((b , s) , child) =
        ΣPathP (refl , (retFC1 (F b) w (s , child)))
      retFC1 (⊗e Fl Fr) w ((splits , sl , sr) , child) = ΣPathP (refl , ΣPathP
        ( retFC1 Fl _ (sl , λ p → child (inl p))
        , retFC1 Fr _ (sr , λ p → child (inr p))))

      retFC2 : ∀ (F : Functor A) w t →
        PathP
          (λ i → (p : FP F w (retFC1 F w t i)) →
            g (F-inX F w (retFC1 F w t i) p .fst) (F-inX F w (retFC1 F w t i) p .snd))
        ((toContainer F ∘g fromContainer F) w t .snd)
        (t .snd)
      retFC2 (Var a) w _ = refl
      retFC2 (k g) w _ = isContr→isProp isContrΠ⊥* _ _
      retFC2 (⊕e B F) w ((b , s) , child) = retFC2 (F b) w (s , child)
      retFC2 (&e B F) w (s , child) i (b , p) = retFC2 (F b) w (s b , (λ p → child (b , p))) i p
      retFC2 (⊗e Fl Fr) w ((_ , sl , sr) , child) i (inl p) = retFC2 Fl _ (sl , λ p → child (inl p)) i p
      retFC2 (⊗e Fl Fr) w ((_ , sl , sr) , child) i (inr p) = retFC2 Fr _ (sr , λ p → child (inr p)) i p

      retFC : ∀ (F : Functor A) w t → (toContainer F ∘g fromContainer F) w t ≡ t
      retFC F w t = ΣPathP ((retFC1 F w t) , retFC2 F w t)

      F≅Container :
        ∀ (F : Functor A) → StrongEquivalence (Container F g) (⟦ F ⟧ g)
      F≅Container F .fun = fromContainer F
      F≅Container F .inv = toContainer F
      F≅Container F .sec = funExt λ w → funExt (secFC F w)
      F≅Container F .ret = funExt λ w → funExt (retFC F w)

  --   isMap : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}(F : Functor A)
  --     → ∀ w a
  --     → (t : ⟦ F ⟧ g w)
  --     → (f : ∀ a → g a ⊢ h a)
  --     → nodeF F w a (getShapeF F w t) (λ p → f _ _ (getSubtreeF g F w a t p))
  --       ≡ SPF.map F f w t
  --   isMap (k g) w a t f = refl
  --   isMap (Var a') w a t f = refl
  --   isMap (&e B F) w a t f i b = isMap (F b) w a (t b) f i
  --   isMap (⊕e B F) w a (b , t) f i = b , isMap (F b) w a t f i
  --   isMap (⊗e Fl Fr) w a (splits , tl , tr) f i =
  --     splits , isMap Fl _ a tl f i , isMap Fr _ a tr f i 

  -- module _ (F : A → Functor A) where
  --   μ : A → Grammar ℓ
  --   μ a s = IW (λ ix → FS (F (ix .fst)) (ix .snd))
  --           (λ ix → FP (F (ix .fst)) (ix .snd))
  --           (λ ix → F-inX (F (ix .fst)) ix) (a , s)

  --   roll : ∀ a → ⟦ F a ⟧ μ ⊢ μ a
  --   roll a w t = node (getShapeF (F a) _ t) (getSubtreeF μ (F a) w a t)

  --   initialAlgebra : Algebra F μ
  --   initialAlgebra = roll

  --   module _ {g : A → Grammar ℓ'} (α : Algebra F g) where
  --     rec : ∀ a → μ a ⊢ g a
  --     rec a w (node s subtree) =
  --       α a w (nodeF (F a) w a s (λ p → rec _ _ (subtree p)))

  --     recHomo : Homomorphism F roll α
  --     recHomo .fst = rec
  --     recHomo .snd a = funExt λ w → funExt λ t → cong (α a w) (isMap (F a) w a t rec)

  --     private
  --       re-wrap : ∀ a w s subtree
  --         → (node s subtree) ≡ roll a w (nodeF (F a) w a s subtree)
  --       re-wrap = {!!}

  --     module _ (ϕ : Homomorphism F initialAlgebra α) where
  --       private
  --         ϕ-lem : ∀ a w s subtree
  --           → ϕ .fst a w (node s subtree)
  --             ≡ α a w (nodeF (F a) w a s (λ p → ϕ .fst _ _ (subtree p)))
  --         ϕ-lem a w s subtree = {!!}

  --       η' : ∀ a w x → ϕ .fst a w x ≡ rec a w x
  --       η' a w (node s subtree) =
  --         cong (ϕ .fst a w) (re-wrap _ _ s subtree) 
  --         ∙ (λ i → ϕ .snd a i w (nodeF (F a) w a s subtree))
  --         ∙ cong (α a w)
  --           (sym (isMap (F a) w a (nodeF (F a) w a s subtree) (ϕ .fst))
  --           ∙ {!!}
  --           ∙ cong (nodeF (F a) w a s) (funExt λ p → η' _ _ (subtree p)))
  --         -- ∙ (λ i → α a w (isMap (F a) w a (nodeF (F a) w a s subtree) (ϕ .fst) (~ i)))
  --         -- ∙ {!!}
  --         -- ∙ (λ i → α a w (nodeF (F a) w a s (λ p → η' _ _ (subtree p) i)))

  --       η : ϕ .fst ≡ rec
  --       η = funExt λ a → funExt λ w → funExt (η' a w)
