{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
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

  @0 _⊗Path_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⊗Path B) w = Σ[ s ∈ SplittingPath w ] A (s .fst .fst) × B (s .fst .snd)

  @0 ⊗→⊗Path : A ⊗ B ⊢ A ⊗Path B
  ⊗→⊗Path _ (s , a , b) = Splitting→SplittingPath _ s , a , b

  @0 ⊗Path→⊗ : A ⊗Path B ⊢ A ⊗ B
  ⊗Path→⊗ _ (s , a , b) = SplittingPath→Splitting _ s , a , b

  @0 isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  isSetGrammar⊗ isSetG isSetB w = isSetΣ (isSetSplitting w)
    λ _ → isSet× (isSetG _) (isSetB _)

infixr 25 _⊗_

opaque
  unfolding _⊗_
  -- Needed because ⊗ is opaque, so that the interface of
  -- ⊗ doesn't leak in type signatures
  the-split :
    ∀ {w : String} → (p : (A ⊗ B) w) → Splitting w
  the-split p = p .fst

  @0 the-splitPath :
    ∀ {w : String} → (p : (A ⊗Path B) w) → SplittingPath w
  the-splitPath p = p .fst

opaque
  unfolding _⊗_ the-split

  same-parses :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → (p : (A i0 ⊗ B i0) (w i0))
    → (q : (A i1 ⊗ B i1) (w i1))
    → (s≡ : PathP (λ i → Splitting (w i)) (the-split p) (the-split q))
    → Type (ℓ-max ℓA ℓB)
  same-parses {A = A} {B = B} p q s≡ =
    PathP (λ i → A i (s≡ i .fst .fst) × B i (s≡ i .fst .snd)) (p .snd) (q .snd)

  @0 same-parsesPath :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → (p : (A i0 ⊗Path B i0) (w i0))
    → (q : (A i1 ⊗Path B i1) (w i1))
    → (s≡ : PathP (λ i → SplittingPath (w i)) (the-splitPath p) (the-splitPath q))
    → Type (ℓ-max ℓA ℓB)
  same-parsesPath {A = A} {B = B} p q s≡ =
    PathP (λ i → A i (s≡ i .fst .fst) × B i (s≡ i .fst .snd)) (p .snd) (q .snd)

  @0 ⊗PathP :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → {p : (A i0 ⊗ B i0) (w i0)}
    → {q : (A i1 ⊗ B i1) (w i1)}
    → (s≡ : PathP (λ i → Splitting (w i)) (the-split p) (the-split q))
    → same-parses {A = A} {B = B} {w = w} p q s≡
    → PathP (λ i → (A i ⊗ B i) (w i)) p q
  ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP (λ i → (s≡ i .fst .fst) , (s≡ i .fst .snd)) , p≡)

  @0 ⊗Path-PathP :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → {p : (A i0 ⊗Path B i0) (w i0)}
    → {q : (A i1 ⊗Path B i1) (w i1)}
    → (s≡ : PathP (λ i → SplittingPath (w i)) (the-splitPath p) (the-splitPath q))
    → same-parsesPath {A = A} {B = B} {w = w} p q s≡
    → PathP (λ i → (A i ⊗Path B i) (w i)) p q
  ⊗Path-PathP s≡ p≡ = ΣPathP (SplittingPath-PathP (λ i → (s≡ i .fst .fst) , (s≡ i .fst .snd)) , p≡)

  @0 ⊗≡ : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{w}
    → (p p' : (A ⊗ B) w)
    → (s≡ : the-split p ≡ the-split p')
    → same-parses {A = λ _ → A} {B = λ _ → B} {w = λ _ → w} p p' s≡
    → p ≡ p'
  ⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡

opaque
  unfolding _⊗_
  ⊗-intro :
    A ⊢ B →
    C ⊢ D →
    A ⊗ C ⊢ B ⊗ D
  ⊗-intro e e' _ p =
    p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

  @0 ⊗Path-intro :
    A ⊢ B →
    C ⊢ D →
    A ⊗Path C ⊢ B ⊗Path D
  ⊗Path-intro e e' _ p =
    p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

opaque
  unfolding _⊗_ the-split ⊗-intro ⊗≡
  ⊗-intro⊗-intro
    : ∀ {f : A ⊢ B}{f' : C ⊢ D}
        {f'' : E ⊢ A}
        {f''' : F ⊢ C}
    → ⊗-intro f f' ∘g ⊗-intro f'' f'''
      ≡ ⊗-intro (f ∘g f'') (f' ∘g f''')
  ⊗-intro⊗-intro = refl

  opaque
    unfolding ε
    ⊗-unit-r :
      A ⊗ ε ⊢ A
    ⊗-unit-r {A = A} w ((_ , Eq.refl) , a , Eq.refl) =
      Eq.J (λ u v → A u) a (Eq.sym (++-unit-r-Eq _))

    @0 ⊗Path-unit-r :
      A ⊗Path εPath ⊢ A
    ⊗Path-unit-r {A = A} _ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) =
      subst A (sym (++-unit-r _)
              ∙ cong (w' ++_) (sym []'≡[])
              ∙ sym w≡w'++[]')
            p⟨w'⟩

    ⊗-unit-r⁻ :
      A ⊢ A ⊗ ε
    ⊗-unit-r⁻ w p =
      ((w , []) , Eq.sym (++-unit-r-Eq w)) , p , ε-intro

    @0 ⊗Path-unit-r⁻ :
      A ⊢ A ⊗Path εPath
    ⊗Path-unit-r⁻ _ p =
      ((_ , []) , (sym (++-unit-r _))) , (p , refl)

--     @0 rectify :
--       ∀ {w w'}{A : Grammar ℓA}
--       → {p : A w}{q : A w'}
--       → {w≡ w≡' : w ≡ w'}
--       → PathP (λ i → A (w≡  i)) p q
--       → PathP (λ i → A (w≡' i)) p q
--     rectify {w = w}{w'}{A = A}{p = p}{q = q} =
--       subst {A = w ≡ w'} (λ w≡ → PathP (λ i → A (w≡ i)) p q)
--         (isSetString _ _ _ _)

--     @0 ⊗-unit-rr⁻ :
--       ∀ {A : Grammar ℓA}
--       → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
--     ⊗-unit-rr⁻ {A = A} =
--       funExt λ w → funExt λ where
--         ((ws , Eq.refl) , a , Eq.refl) →
--           {!!}

-- --     ⊗-unit-r⁻r : ∀ {A : Grammar ℓA}
-- --       → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
-- --     ⊗-unit-r⁻r {A = A} = funExt λ w → funExt λ where
-- --       a → {!!}
-- -- --       t
-- -- --         w≡w : w ≡ w
-- -- --         w≡w =       (λ i →
-- -- --              (hcomp
-- -- --               (doubleComp-faces (λ _ → w)
-- -- --                (λ i₁ →
-- -- --                   hcomp (doubleComp-faces (λ _ → w ++ [])
-- -- --                     (λ i₂ → ++-unit-r w i₂) i₁)
-- -- --                   (w ++ []))
-- -- --                i)
-- -- --               (++-unit-r w (~ i))))
-- -- --       in
-- -- --       subst (λ w≡w → subst A w≡w p ≡ p) (isSetString _ _ refl w≡w)
-- -- --         (substRefl {B = A} p)

-- --     ⊗-unit-l :
-- --       ε ⊗ A ⊢ A
-- --     ⊗-unit-l {A = A} _ ((_ , Eq.refl) , Eq.refl , a) = a

-- --     ⊗-unit-l⁻ :
-- --       A ⊢ ε ⊗ A
-- --     ⊗-unit-l⁻ _ p = (_ , Eq.refl) , ε-intro , p

-- --     @0 ⊗-unit-ll⁻ :
-- --       ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
-- --     ⊗-unit-ll⁻ {A = A} =
-- --       funExt λ w → funExt λ where
-- --         ((_ , Eq.refl) , Eq.refl , a) → refl

-- --     @0 ⊗-unit-l⁻l :
-- --       ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id
-- --     ⊗-unit-l⁻l {A = A} = refl

-- --     @0 cong-∘g⊗-unit-l⁻ :
-- --       (e e' : ε ⊗ A ⊢ B) →
-- --       (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
-- --       e ≡ e'
-- --     cong-∘g⊗-unit-l⁻ f A ∘g≡ =
-- --       cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
-- --       cong (_∘g ⊗-unit-l) ∘g≡ ∙
-- --       cong (A ∘g_) (⊗-unit-ll⁻)

-- --     @0 cong-∘g⊗-unit-r⁻ :
-- --       (e e' : A ⊗ ε ⊢ B) →
-- --       (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
-- --       e ≡ e'
-- --     cong-∘g⊗-unit-r⁻ {A = A} f f' ∘g≡ =
-- --       cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
-- --       cong (_∘g ⊗-unit-r) ∘g≡ ∙
-- --       cong (f' ∘g_) (⊗-unit-rr⁻)


-- --     @0 ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
-- --     ⊗-unit-rl⁻ =
-- --       funExt λ w → funExt λ where
-- --         Eq.refl → refl

-- --     --technically this follows from more basic monoidal category axioms but it's not simple
-- --     @0 ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id
-- --     ⊗-unit-lr⁻ = funExt λ w → funExt λ where
-- --       Eq.refl → refl

-- --   ⊗-assoc :
-- --     A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
-- --   ⊗-assoc _ (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) =
-- --     ((wa ++ wb , wc) , Eq.sym (++-assoc-Eq wa wb wc)) , ((((wa , wb) , Eq.refl) , (a , b)) , c)

-- --   ⊗-assoc⁻ :
-- --     (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
-- --   ⊗-assoc⁻ _ (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) =
-- --     ((wa , wb ++ wc) , ++-assoc-Eq wa wb wc) , (a , (((wb , wc) , Eq.refl) , (b , c)))

-- --   @0 ⊗-assoc∘⊗-assoc⁻≡id :
-- --    ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
-- --   ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ where
-- --     (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) →
-- --       ⊗≡ _ _
-- --         (≡-× (λ i → {!!}) {!!})
-- --         {!!}
-- -- --     ⊗≡ _ _
-- -- --       (≡-× (λ i → p .snd .fst .fst .snd (~ i)) refl)
-- -- --       (ΣPathP (
-- -- --         (⊗PathP
-- -- --           (≡-× refl refl)
-- -- --           (≡-× refl refl)) ,
-- -- --         refl))

-- -- --   ⊗-assoc⁻∘⊗-assoc≡id :
-- -- --    ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
-- -- --   ⊗-assoc⁻∘⊗-assoc≡id = funExt λ w → funExt λ p →
-- -- --     ⊗≡ _ _
-- -- --       (≡-× refl (sym (p .snd .snd .fst .snd)))
-- -- --       (ΣPathP (
-- -- --         refl ,
-- -- --         (⊗PathP (≡-× refl refl)
-- -- --           (ΣPathP (refl , refl)))))

-- -- --   ⊗-assoc⁻⊗-intro :
-- -- --     ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
-- -- --     → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
-- -- --     ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
-- -- --   ⊗-assoc⁻⊗-intro = refl

-- -- --   ⊗-assoc⊗-intro :
-- -- --     ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
-- -- --     → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
-- -- --       ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
-- -- --   ⊗-assoc⊗-intro = funExt λ w → funExt λ p →
-- -- --     ⊗≡ _ _ (≡-× refl refl) (ΣPathP (refl , refl))

-- -- --   opaque
-- -- --     unfolding ⊗-unit-r⁻
-- -- --     ⊗-assoc⁻⊗-unit-r⁻ :
-- -- --       ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
-- -- --     ⊗-assoc⁻⊗-unit-r⁻ = funExt λ w → funExt λ p →
-- -- --       ⊗≡ _ _ (≡-× refl (++-unit-r _))
-- -- --         (ΣPathP (refl , ⊗PathP refl refl))

-- -- --   opaque
-- -- --     unfolding ⊗-unit-l⁻
-- -- --     ⊗-assoc⊗-unit-l⁻ :
-- -- --      ⊗-assoc {A = A}{C = C} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
-- -- --     ⊗-assoc⊗-unit-l⁻ = funExt λ w → funExt λ p →
-- -- --       ⊗≡ _ _ (≡-× (++-unit-r _) refl) (ΣPathP (⊗PathP refl refl , refl))

-- -- --   opaque
-- -- --     unfolding ε ⊗-unit-l⁻
-- -- --     ⊗-unit-l⁻⊗-intro :
-- -- --       ∀ {f : A ⊢ B}
-- -- --       → ⊗-unit-l⁻ ∘g f
-- -- --       ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
-- -- --     ⊗-unit-l⁻⊗-intro = refl

-- -- --     ⊗-unit-l⊗-intro :
-- -- --       ∀ (f : A ⊢ B)
-- -- --       → f ∘g ⊗-unit-l
-- -- --         ≡ ⊗-unit-l ∘g (⊗-intro id f)
-- -- --     ⊗-unit-l⊗-intro f =
-- -- --       cong-∘g⊗-unit-l⁻ _ _
-- -- --         λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

-- -- --     ⊗-unit-r⁻⊗-intro :
-- -- --       ∀ {f : A ⊢ B}
-- -- --       → ⊗-unit-r⁻ ∘g f
-- -- --       ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
-- -- --     ⊗-unit-r⁻⊗-intro = refl

-- -- --     -- this is the fact that the inverse of a natural transformation is natural
-- -- --     ⊗-unit-r⊗-intro :
-- -- --       (f : A ⊢ B) →
-- -- --       ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
-- -- --     ⊗-unit-r⊗-intro f =
-- -- --       cong-∘g⊗-unit-r⁻ _ _
-- -- --         (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

-- -- --     id,⊗id≡id : ⊗-intro id id ≡ id {A = A ⊗ B}
-- -- --     id,⊗id≡id = refl

-- -- -- _,⊗_ = ⊗-intro
-- -- -- infixr 20 _,⊗_

-- -- -- {- ε* versions of the unitors  -}
-- -- -- ⊗-unit*-l : ε* {ℓ} ⊗ A ⊢ A
-- -- -- ⊗-unit*-l = ⊗-unit-l ∘g ⊗-intro lowerG id

-- -- -- ⊗-unit*-l⁻ : A ⊢ ε* {ℓ} ⊗ A
-- -- -- ⊗-unit*-l⁻ = ⊗-intro liftG id ∘g ⊗-unit-l⁻

-- -- -- opaque
-- -- --   unfolding ⊗-intro
-- -- --   ⊗-unit*-l⊗-intro :
-- -- --       ∀ (f : A ⊢ B)
-- -- --       → f ∘g ⊗-unit*-l {ℓ}
-- -- --         ≡ ⊗-unit*-l ∘g (⊗-intro id f)
-- -- --   ⊗-unit*-l⊗-intro f =
-- -- --     cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl
-- -- --   ⊗-unit*-ll⁻ :
-- -- --     ⊗-unit*-l⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-l ≡ id
-- -- --   ⊗-unit*-ll⁻ i = ⊗-intro liftG id ∘g ⊗-unit-ll⁻ i ∘g ⊗-intro lowerG id

-- -- --   ⊗-unit*-l⁻l :
-- -- --     ⊗-unit*-l {ℓ = ℓ} {A = A} ∘g ⊗-unit*-l⁻ ≡ id
-- -- --   ⊗-unit*-l⁻l = ⊗-unit-l⁻l

-- -- -- ⊗-unit*-r : A ⊗ ε* {ℓ} ⊢ A
-- -- -- ⊗-unit*-r = ⊗-unit-r ∘g ⊗-intro id lowerG

-- -- -- ⊗-unit*-r⁻ : A ⊢ A ⊗ ε* {ℓ}
-- -- -- ⊗-unit*-r⁻ = ⊗-intro id liftG ∘g ⊗-unit-r⁻

-- -- -- opaque
-- -- --   unfolding ⊗-intro
-- -- --   ⊗-unit*-r⊗-intro :
-- -- --       ∀ (f : A ⊢ B)
-- -- --       → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
-- -- --         ≡ f ∘g ⊗-unit*-r
-- -- --   ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

-- -- --   ⊗-unit*-rr⁻ :
-- -- --     ⊗-unit*-r⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r ≡ id
-- -- --   ⊗-unit*-rr⁻ {A = A} {ℓ = ℓ} i = ⊗-intro id liftG ∘g ⊗-unit-rr⁻ {A = A} i ∘g ⊗-intro id lowerG

-- -- --   ⊗-unit*-r⁻r :
-- -- --     ⊗-unit*-r {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r⁻ ≡ id
-- -- --   ⊗-unit*-r⁻r = ⊗-unit-r⁻r

-- -- -- {- Triangle -}
-- -- -- opaque
-- -- --   unfolding ⊗-intro ⊗-unit-r ⊗-unit-l ⊗-assoc
-- -- --   ⊗-triangle :
-- -- --     ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {A = A}{B = ε* {ℓ}}{C = B}
-- -- --     ≡ ⊗-intro id ⊗-unit*-l
-- -- --   ⊗-triangle {A = A}{B = B} = funExt λ w → funExt λ {
-- -- --     (((w1 , w2) , w≡w1w2) ,
-- -- --      (gp , (((w3 , w4) , w2≡w3w4) , ((lift w3≡[]) , Bp)))) →
-- -- --     let p1 : w1 ++ w3 ≡ w1
-- -- --         p1 = (cong (w1 ++_) w3≡[] ∙ ++-unit-r _)
-- -- --         p2 = (cong (_++ w4) (sym w3≡[]) ∙ sym w2≡w3w4)
-- -- --         p1' : w1 ≡ w1 ++ w3
-- -- --         p1' = λ i → (hcomp
-- -- --            (doubleComp-faces (λ _ → w1)
-- -- --             (λ i₁ →
-- -- --                hcomp (doubleComp-faces (λ _ → w1 ++ []) (λ i₂ → w1 ++ w3) i₁)
-- -- --                (w1 ++ w3≡[] (~ i₁)))
-- -- --             i)
-- -- --            (++-unit-r w1 (~ i)))
-- -- --     in
-- -- --     ⊗≡ _ _ (≡-× p1 p2)
-- -- --      (ΣPathP (rectify {A = A} {w≡ = sym p1'}{w≡' = p1}
-- -- --        (symP (transport-filler (cong A p1') gp))
-- -- --      , transport-filler (cong B p2) Bp))
-- -- --     }

-- -- -- {- Pentagon -}
-- -- -- opaque
-- -- --   unfolding ⊗-intro ⊗-assoc
-- -- --   ⊗-pentagon :
-- -- --     ⊗-intro (⊗-assoc {A = A}) id
-- -- --     ∘g ⊗-assoc
-- -- --     ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D})
-- -- --       ≡
-- -- --     ⊗-assoc
-- -- --     ∘g ⊗-assoc
-- -- --   ⊗-pentagon {A = A}{B = B}{C = C}{D = D} =
-- -- --     funExt λ w → funExt λ {
-- -- --     (((w1 , w234) , w≡w1w234) , p1 ,
-- -- --     (((w2 , w34) , w234≡w2w34) , p2 ,
-- -- --     (((w3 , w4) , w34≡w3w4) , (p3 , p4)))) →
-- -- --     ⊗≡ _ _
-- -- --     (≡-× (sym (++-assoc w1 w2 w3)) refl)
-- -- --     (ΣPathP ((⊗PathP (≡-× refl refl) refl) , refl))
-- -- --     }

-- -- -- {- Big associators and big diagrams -}

-- -- -- ⊗-assoc⁻3 :
-- -- --   (A ⊗ B ⊗ C) ⊗ D ⊢ A ⊗ B ⊗ C ⊗ D
-- -- -- ⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

-- -- -- ⊗-assoc3 :
-- -- --   A ⊗ B ⊗ C ⊗ D ⊢ (A ⊗ B ⊗ C) ⊗ D
-- -- -- ⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

-- -- -- ⊗-assoc⁻3⊗-unit-r⁻ :
-- -- --   ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
-- -- --   ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- -- -- ⊗-assoc⁻3⊗-unit-r⁻ =
-- -- --   cong (id ,⊗ ⊗-assoc⁻ ∘g_) ⊗-assoc⁻⊗-unit-r⁻
-- -- --   ∙ ⊗-intro⊗-intro
-- -- --   ∙ cong (id ,⊗_) ⊗-assoc⁻⊗-unit-r⁻

-- -- -- ⊗-assoc⁻4 :
-- -- --   (A ⊗ B ⊗ C ⊗ D) ⊗ E ⊢ A ⊗ B ⊗ C ⊗ D ⊗ E
-- -- -- ⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

-- -- -- ⊗-assoc4 :
-- -- --   A ⊗ B ⊗ C ⊗ D ⊗ E ⊢ (A ⊗ B ⊗ C ⊗ D) ⊗ E
-- -- -- ⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3

-- -- -- ⊗-assoc⁻4⊗-unit-r⁻ :
-- -- --   ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-unit-r⁻
-- -- --   ≡ id ,⊗ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- -- -- ⊗-assoc⁻4⊗-unit-r⁻ =
-- -- --   cong (id ,⊗ ⊗-assoc⁻3 ∘g_) ⊗-assoc⁻⊗-unit-r⁻
-- -- --   ∙ ⊗-intro⊗-intro
-- -- --   ∙ cong (id ,⊗_) ⊗-assoc⁻3⊗-unit-r⁻

-- -- -- opaque
-- -- --   unfolding ⊗-intro ⊗-assoc
-- -- --   ⊗-assoc⁻4⊗-intro :
-- -- --     ∀ {f f' f'' f''' f''''} →
-- -- --     (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
-- -- --     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
-- -- --   ⊗-assoc⁻4⊗-intro = refl

-- -- -- opaque
-- -- --   unfolding ⊗-intro ⊗-assoc
-- -- --   ⊗-assoc3⊗-assoc⁻3 : ⊗-assoc3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc⁻3 ≡ id
-- -- --   ⊗-assoc3⊗-assoc⁻3 =
-- -- --     ⊗-assoc ∘g id ,⊗ ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
-- -- --       ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc∘⊗-assoc⁻≡id i ∘g ⊗-assoc⁻) ⟩
-- -- --     ⊗-assoc ∘g ⊗-assoc⁻
-- -- --     ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩ id ∎

-- -- --   ⊗-assoc4⊗-assoc⁻4 : ⊗-assoc4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g ⊗-assoc⁻4 ≡ id
-- -- --   ⊗-assoc4⊗-assoc⁻4 =
-- -- --     ⊗-assoc ∘g id ,⊗ ⊗-assoc3 ∘g id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻
-- -- --       ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc3⊗-assoc⁻3 i ∘g ⊗-assoc⁻) ⟩
-- -- --     ⊗-assoc ∘g ⊗-assoc⁻
-- -- --       ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
-- -- --     id ∎

-- -- --   ⊗-assoc⁻3⊗-assoc3 : ⊗-assoc⁻3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc3 ≡ id
-- -- --   ⊗-assoc⁻3⊗-assoc3 =
-- -- --     id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
-- -- --       ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc) ⟩
-- -- --     id ,⊗ (⊗-assoc⁻ ∘g ⊗-assoc) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻∘⊗-assoc≡id i)) ⟩
-- -- --     id ∎

-- -- --   ⊗-assoc⁻4⊗-assoc4 : ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E}∘g ⊗-assoc4 ≡ id
-- -- --   ⊗-assoc⁻4⊗-assoc4 =
-- -- --     id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc3
-- -- --       ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc3) ⟩
-- -- --     id ,⊗ (⊗-assoc⁻3 ∘g ⊗-assoc3) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻3⊗-assoc3 i)) ⟩
-- -- --     id ∎

-- -- --   ⊗-assoc4⊗-intro :
-- -- --     ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
-- -- --     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
-- -- --   ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
-- -- --     sym (invMoveR {f = ⊗-assoc⁻4} {f⁻ = ⊗-assoc4} ⊗-assoc4⊗-assoc⁻4
-- -- --       (cong ((f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''') ∘g_) ⊗-assoc⁻4⊗-assoc4))

-- -- -- open StrongEquivalence
-- -- -- module _
-- -- --   {A : Grammar ℓA} {B : Grammar ℓB}
-- -- --   {C : Grammar ℓC} {D : Grammar ℓD}
-- -- --   (A≅B : A ≅ B)
-- -- --   (C≅D : C ≅ D)
-- -- --   where

-- -- --   private
-- -- --     the-fun : A ⊗ C ⊢ B ⊗ D
-- -- --     the-fun = A≅B .fun ,⊗ C≅D .fun

-- -- --     the-inv : B ⊗ D ⊢ A ⊗ C
-- -- --     the-inv = A≅B .inv ,⊗ C≅D .inv
-- -- --     opaque
-- -- --       unfolding ⊗-intro
-- -- --       the-sec : the-fun ∘g the-inv ≡ id
-- -- --       the-sec i = A≅B .sec i ,⊗ C≅D .sec i

-- -- --       the-ret : the-inv ∘g the-fun ≡ id
-- -- --       the-ret i = A≅B .ret i ,⊗ C≅D .ret i

-- -- --   ⊗≅ : (A ⊗ C) ≅ (B ⊗ D)
-- -- --   ⊗≅ .fun = the-fun
-- -- --   ⊗≅ .inv = the-inv
-- -- --   ⊗≅ .sec = the-sec
-- -- --   ⊗≅ .ret = the-ret

-- -- -- module _
-- -- --   {A : Grammar ℓA}
-- -- --   {B : Grammar ℓB}
-- -- --   {C : Grammar ℓC}
-- -- --   where
-- -- --   ⊗-assoc≅ : A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C
-- -- --   ⊗-assoc≅ .fun = ⊗-assoc
-- -- --   ⊗-assoc≅ .inv = ⊗-assoc⁻
-- -- --   ⊗-assoc≅ .sec = ⊗-assoc∘⊗-assoc⁻≡id
-- -- --   ⊗-assoc≅ .ret = ⊗-assoc⁻∘⊗-assoc≡id

-- -- -- εr≅ : A ≅ A ⊗ ε
-- -- -- εr≅ .fun = ⊗-unit-r⁻
-- -- -- εr≅ .inv = ⊗-unit-r
-- -- -- εr≅ .sec = ⊗-unit-rr⁻
-- -- -- εr≅ .ret = ⊗-unit-r⁻r

-- -- -- εl≅ : A ≅ ε ⊗ A
-- -- -- εl≅ .fun = ⊗-unit-l⁻
-- -- -- εl≅ .inv = ⊗-unit-l
-- -- -- εl≅ .sec = ⊗-unit-ll⁻
-- -- -- εl≅ .ret = ⊗-unit-l⁻l
