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

open StrongEquivalence

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

  module _ (F : A → Functor A) where
    Algebra' : (A → Grammar ℓ') → Type (ℓ-max ℓ ℓ')
    Algebra' g = ∀ a → Container (F a) g ⊢ g a

    isHomo' : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}
      → Algebra' g
      → Algebra' h
      → (∀ a → g a ⊢ h a)
      → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isHomo' α β f = ∀ a → f a ∘g α a ≡ β a ∘g map (F a) f

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

  module _ (F : A → Functor A) where
    Algebra→Algebra' : ∀ {g : A → Grammar ℓ'}
      → Algebra F g
      → Algebra' F g
    Algebra→Algebra' α a = α a ∘g fromContainer (F a)

  opaque
    unfolding fromContainer
    fromContainerMap  : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}(F : Functor A)
      → (f : ∀ a → g a ⊢ h a)
      → fromContainer F ∘g map F f ≡ SPF.map F f ∘g fromContainer F
    fromContainerMap (k g) f = refl
    fromContainerMap (Var a) f = refl
    fromContainerMap (⊕e B F) f i w ((b , s) , child) =
      b , (fromContainerMap (F b) f i w (s , child))
    fromContainerMap (&e B F) f i w (s , child) b =
      fromContainerMap (F b) f i w (s b , λ p → child (b , p))
    fromContainerMap (⊗e Fl Fr) f i w ((splits , sl , sr) , child) =
      splits
      , fromContainerMap Fl f i _ (sl , λ p → child (inl p))
      , fromContainerMap Fr f i _ (sr , λ p → child (inr p))

  module _ (F : A → Functor A) where
    μ : A → Grammar ℓ
    μ a s = IW (λ ix → FS (F (ix .fst)) (ix .snd))
            (λ ix → FP (F (ix .fst)) (ix .snd))
            (λ ix → F-inX (F (ix .fst)) (ix .snd)) (a , s)

    ContainerToμ : ∀ a → Container (F a) μ ⊢ μ a
    ContainerToμ a w (s , child) = node s child

    roll : ∀ a → ⟦ F a ⟧ μ ⊢ μ a
    roll a = ContainerToμ a ∘g toContainer (F a)

    initialAlgebra : Algebra F μ
    initialAlgebra = roll

    initialAlgebra' : Algebra' F μ
    initialAlgebra' = λ a w z → node (z .fst) (z .snd)

    initAlgFromContainer : ∀ a → initialAlgebra' a ≡ initialAlgebra a ∘g fromContainer (F a)
    initAlgFromContainer a = cong (ContainerToμ a ∘g_) (sym (F≅Container (F a) .ret))


    module _ {g : A → Grammar ℓ'} where
      module _ (α : Algebra' F g) where
        rec' : ∀ a → μ a ⊢ g a
        rec' a w (node s child) = α a w (s , (λ p → rec' _ _ (child p)))

        rec'IsHomo : isHomo' F initialAlgebra' α rec'
        rec'IsHomo a = refl

        module _ (f : ∀ a → μ a ⊢ g a) (fIsHomo' : isHomo' F initialAlgebra' α f) where
          η'' : ∀ a w t → f a w t ≡ rec' a w t
          η'' a w (node s subtree) = funExt⁻ (funExt⁻ (fIsHomo' a) w) (s , subtree)
            ∙ λ i → α a w (s , (λ p → η'' _ _ (subtree p) i))

    module _ {g : A → Grammar ℓ'} (α : Algebra F g) where
      rec : ∀ a → μ a ⊢ g a
      rec = rec' (Algebra→Algebra' F α)

      opaque
        unfolding toContainer
        recIsHomo : isHomo F initialAlgebra α rec
        recIsHomo a = cong (α a ∘g_)
          (cong (_∘g toContainer (F a)) (fromContainerMap (F a) rec)
          ∙ cong (SPF.map (F a) rec ∘g_) (F≅Container (F a) .sec))

      module _  (f : ∀ a → μ a ⊢ g a) (fIsHomo : isHomo F initialAlgebra α f) where
        private
          fIsHomo' : isHomo' F initialAlgebra' (Algebra→Algebra' F α) f
          fIsHomo' a =
            cong (f a ∘g_) (initAlgFromContainer a)
            ∙ cong (_∘g fromContainer (F a)) (fIsHomo a)
            ∙ cong (α a ∘g_) (sym (fromContainerMap (F a) f))

        η' : ∀ a w t → f a w t ≡ rec a w t
        η' = η'' (Algebra→Algebra' F α) f fIsHomo'

        η : ∀ a → f a ≡ rec a
        η a = funExt₂ (η' a)

    unroll : ∀ a → μ a ⊢ ⟦ F a ⟧ μ
    unroll = rec λ a → SPF.map (F a) roll
