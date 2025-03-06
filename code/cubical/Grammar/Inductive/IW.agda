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
open import Grammar.Inductive.Functor Alphabet as SPF hiding (map)
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX ℓ ℓ' ℓ'' ℓ''' : Level

open StrongEquivalence

module _ {X : Type ℓX} where
  FS : (F : Functor X) → String → Type ℓX
  FS F = ⟦ F ⟧ (λ x w  → Unit* {ℓX})
  opaque
    unfolding _⊗_

    FP : (F : Functor X) → (w : String) → FS F w → Type ℓX
    FP (k g) w s = ⊥*
    FP (Var a') w s = Unit*
    FP (&e B F) w s = Σ[ b ∈ B ] FP (F b) w (s b)
    FP (⊕e B F) w (b , s) = FP (F b) w s
    FP (Fl ⊗e Fr) _ (((wl , wr), _) , sl , sr) = FP Fl wl sl ⊎ FP Fr wr sr

    F-inX : (F : Functor X) (w : String) (s : FS F w)
      (p : FP F w s)
      → X × String
    F-inX (Var a) w s p = a , w
    F-inX (&e B F) w s (b , p) = F-inX (F b) w (s b) p
    F-inX (⊕e B F) w (b , s) p = F-inX (F b) w s p
    F-inX (Fl ⊗e Fr) _ (sp , sl , sr) (inl p) =
      F-inX Fl (sp .fst .fst) sl p
    F-inX (Fl ⊗e Fr) _ (sp , sl , sr) (inr p) =
      F-inX Fr (sp .fst .snd) sr p

  Container : (F : Functor X) → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
  Container F g w = Σ[ s ∈ FS F w ]
    (∀ (p : FP F w s) →
         let ix = F-inX F w s p in
         g (ix .fst) (ix .snd))

  map : ∀ (F : Functor X) {A : X → Grammar ℓA}{B : X → Grammar ℓB}
      → (∀ x → A x ⊢ B x)
      → Container F A ⊢ Container F B
  map F f w (s , child) = s , (λ p → f _ _ (child p))

  module _ (F : X → Functor X) where
    Algebra' : (X → Grammar ℓA) → Type (ℓ-max ℓX ℓA)
    Algebra' A = ∀ x → Container (F x) A ⊢ A x

    isHomo' : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}
      → Algebra' A
      → Algebra' B
      → (∀ x → A x ⊢ B x)
      → Type (ℓ-max (ℓ-max ℓX ℓA) ℓB)
    isHomo' α β f = ∀ x → f x ∘g α x ≡ β x ∘g map (F x) f

  module _ {A : X → Grammar ℓA} where
    getShapeF : {B : X → Grammar ℓA}(F : Functor X)
      → ∀ w
      → ⟦ F ⟧ B w → FS F w
    getShapeF F = SPF.map F λ a w x → tt*

    opaque
      unfolding FP _⊗_ ⊗-intro
      getSubtreeF : (F : Functor X)
        → ∀ w
        → (e : ⟦ F ⟧ A w)
        → (p : FP F w (getShapeF F _ e))
        → let ix = (F-inX F w _ p) in A (ix .fst) (ix .snd)
      getSubtreeF (Var a') w e p = e .lower
      getSubtreeF (&e B F) w e (b , p) = getSubtreeF (F b) w (e b) p
      getSubtreeF (⊕e B F) w (b , e) p = getSubtreeF (F b) w e p
      getSubtreeF (Fl ⊗e Fr) w (((wl , wr) , _) , el , er) (inl pl) =
        getSubtreeF Fl wl el pl
      getSubtreeF (Fl ⊗e Fr) w (((wl , wr) , _) , el , er) (inr pr) =
        getSubtreeF Fr wr er pr

      toContainer : (F : Functor X)
       → ⟦ F ⟧ A ⊢ Container F A
      toContainer F w t = (getShapeF F w t) , getSubtreeF F w t

      fromContainer : ∀ (F : Functor X) → Container F A ⊢ ⟦ F ⟧ A
      fromContainer (k g) _ (s , child) = lift (s .lower)
      fromContainer (Var a) _ (s , child) = lift (child tt*)
      fromContainer (&e B F) _ (s , child) b = fromContainer (F b) _ (s b , (λ p → child (b , p)))
      fromContainer (⊕e B F) _ ((b , s) , child) = b , (fromContainer (F b) _ (s , child))
      fromContainer (Fl ⊗e Fr) _ ((splits , sl , sr) , child) =
       splits
        , (fromContainer Fl _ (sl , λ p → child (inl p)))
        , (fromContainer Fr _ (sr , λ p → child (inr p)))

      secFC : ∀ (F : Functor X) w t → (fromContainer F ∘g toContainer F) w t ≡ t
      secFC (k g) w t = refl
      secFC (Var a) w t = refl
      secFC (&e B F) w t i b = secFC (F b) w (t b) i
      secFC (⊕e B F) w (b , t) i = b , secFC (F b) w t i
      secFC (Fl ⊗e Fr) w (splits , tl , tr) i = splits , (secFC Fl _ tl i , secFC Fr _ tr i)

      retFC1 : ∀ (F : Functor X) w t →
        (toContainer F ∘g fromContainer F) w t .fst ≡ t .fst
      retFC1 (Var a) w t = refl
      retFC1 (k g) w t = refl
      retFC1 (&e B F) w (s , child) = funExt λ b →
        retFC1 (F b) w (s b , (λ p → child (b , p)))
      retFC1 (⊕e B F) w ((b , s) , child) =
        ΣPathP (refl , (retFC1 (F b) w (s , child)))
      retFC1 (Fl ⊗e Fr) w ((splits , sl , sr) , child) = ΣPathP (refl , ΣPathP
        ( retFC1 Fl _ (sl , λ p → child (inl p))
        , retFC1 Fr _ (sr , λ p → child (inr p))))

      retFC2 : ∀ (F : Functor X) w t →
        PathP
          (λ i → (p : FP F w (retFC1 F w t i)) →
            A (F-inX F w (retFC1 F w t i) p .fst) (F-inX F w (retFC1 F w t i) p .snd))
        ((toContainer F ∘g fromContainer F) w t .snd)
        (t .snd)
      retFC2 (Var a) w _ = refl
      retFC2 (k g) w _ = isContr→isProp isContrΠ⊥* _ _
      retFC2 (⊕e B F) w ((b , s) , child) = retFC2 (F b) w (s , child)
      retFC2 (&e B F) w (s , child) i (b , p) = retFC2 (F b) w (s b , (λ p → child (b , p))) i p
      retFC2 (Fl ⊗e Fr) w ((_ , sl , sr) , child) i (inl p) = retFC2 Fl _ (sl , λ p → child (inl p)) i p
      retFC2 (Fl ⊗e Fr) w ((_ , sl , sr) , child) i (inr p) = retFC2 Fr _ (sr , λ p → child (inr p)) i p

      retFC : ∀ (F : Functor X) w t → (toContainer F ∘g fromContainer F) w t ≡ t
      retFC F w t = ΣPathP ((retFC1 F w t) , retFC2 F w t)

    F≅Container :
        ∀ (F : Functor X) → StrongEquivalence (Container F A) (⟦ F ⟧ A)
    F≅Container F .fun = fromContainer F
    F≅Container F .inv = toContainer F
    F≅Container F .sec = funExt λ w → funExt (secFC F w)
    F≅Container F .ret = funExt λ w → funExt (retFC F w)

  module _ (F : X → Functor X) where
    Algebra→Algebra' : ∀ {A : X → Grammar ℓA}
      → Algebra F A
      → Algebra' F A
    Algebra→Algebra' α x = α x ∘g fromContainer (F x)

  opaque
    unfolding fromContainer
    -- fromContainer is a natural isomorphism
    fromContainerNat  : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}(F : Functor X)
      → (f : ∀ x → A x ⊢ B x)
      → fromContainer F ∘g map F f ≡ SPF.map F f ∘g fromContainer F
    fromContainerNat (k A) f = refl
    fromContainerNat (Var x) f = refl
    fromContainerNat (⊕e Y F) f i w ((b , s) , child) =
      b , (fromContainerNat (F b) f i w (s , child))
    fromContainerNat (&e Y F) f i w (s , child) b =
      fromContainerNat (F b) f i w (s b , λ p → child (b , p))
    fromContainerNat (Fl ⊗e Fr) f i w ((splits , sl , sr) , child) =
      splits
      , fromContainerNat Fl f i _ (sl , λ p → child (inl p))
      , fromContainerNat Fr f i _ (sr , λ p → child (inr p))

  module _ (F : X → Functor X) where
    μ : X → Grammar ℓX
    μ x s = IW (λ ix → FS (F (ix .fst)) (ix .snd))
            (λ ix → FP (F (ix .fst)) (ix .snd))
            (λ ix → F-inX (F (ix .fst)) (ix .snd)) (x , s)

    ContainerToμ : ∀ x → Container (F x) μ ⊢ μ x
    ContainerToμ x w (s , child) = node s child

    roll : ∀ x → ⟦ F x ⟧ μ ⊢ μ x
    roll x = ContainerToμ x ∘g toContainer (F x)

    initialAlgebra : Algebra F μ
    initialAlgebra = roll

    initialAlgebra' : Algebra' F μ
    initialAlgebra' = λ x w z → node (z .fst) (z .snd)

    initAlgFromContainer : ∀ x → initialAlgebra' x ≡ initialAlgebra x ∘g fromContainer (F x)
    initAlgFromContainer x = cong (ContainerToμ x ∘g_) (sym (F≅Container (F x) .ret))

    module _ {A : X → Grammar ℓA} where
      module _ (α : Algebra' F A) where
        rec' : ∀ x → μ x ⊢ A x
        rec' x w (node s child) = α x w (s , (λ p → rec' _ _ (child p)))

        rec'IsHomo : isHomo' F initialAlgebra' α rec'
        rec'IsHomo a = refl

        module _ (f : ∀ x → μ x ⊢ A x) (fIsHomo' : isHomo' F initialAlgebra' α f) where
          η'' : ∀ a w t → f a w t ≡ rec' a w t
          η'' a w (node s subtree) = funExt⁻ (funExt⁻ (fIsHomo' a) w) (s , subtree)
            ∙ λ i → α a w (s , (λ p → η'' _ _ (subtree p) i))

    module _ {A : X → Grammar ℓA} (α : Algebra F A) where
      rec : ∀ x → μ x ⊢ A x
      rec = rec' (Algebra→Algebra' F α)

      opaque
        unfolding toContainer
        recIsHomo : isHomo F initialAlgebra α rec
        recIsHomo a = cong (α a ∘g_)
          (cong (_∘g toContainer (F a)) (fromContainerNat (F a) rec)
          ∙ cong (SPF.map (F a) rec ∘g_) (F≅Container (F a) .sec))

      module _  (f : ∀ x → μ x ⊢ A x) (fIsHomo : isHomo F initialAlgebra α f) where
        private
          fIsHomo' : isHomo' F initialAlgebra' (Algebra→Algebra' F α) f
          fIsHomo' x =
            cong (f x ∘g_) (initAlgFromContainer x)
            ∙ cong (_∘g fromContainer (F x)) (fIsHomo x)
            ∙ cong (α x ∘g_) (sym (fromContainerNat (F x) f))

        η' : ∀ x w t → f x w t ≡ rec x w t
        η' = η'' (Algebra→Algebra' F α) f fIsHomo'

        η : ∀ x → f x ≡ rec x
        η x = funExt₂ (η' x)

    unroll : ∀ x → μ x ⊢ ⟦ F x ⟧ μ
    unroll = rec λ x → SPF.map (F x) roll
