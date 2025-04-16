{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
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

  @0 isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  isSetGrammar⊗ isSetG isSetB w = isSetΣ (isSetSplitting w)
    λ _ → isSet× (isSetG _) (isSetB _)

infixr 25 _⊗_

opaque
  unfolding _⊗_
  -- because ⊗ is opaque,
  -- same-splits and same-parses are needed so that the interface of
  -- ⊗ doesn't leak in the type signature of ⊗PathP
  has-split :
    ∀ (w : String) → (p : (A ⊗ B) w) → (s : Splitting w) → Type ℓ-zero
  has-split w p s = s ≡ p .fst

  @0 isProp-has-split : ∀ (w : String) (p : (A ⊗ B) w) → (s : Splitting w) → isProp (has-split w p s)
  isProp-has-split w p s = isSetSplitting w _ _

  the-split :
    ∀ (w : String) → (p : (A ⊗ B) w) → Σ[ s ∈ Splitting w ] has-split w p s
  the-split w p = (p .fst) , refl

same-splits :
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  {D : Grammar ℓD}
  {w : I → String}
  → (p : (A ⊗ B) (w i0))
  → (q : (C ⊗ D) (w i1))
  → Type ℓ-zero
same-splits {w = w} p q =
    (the-split (w i0) p .fst .fst) ≡ (the-split (w i1) q .fst .fst)

opaque
  unfolding _⊗_ the-split

  same-parses :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → (p : (A i0 ⊗ B i0) (w i0))
    → (q : (A i1 ⊗ B i1) (w i1))
    → (s≡ : same-splits {w = w} p q)
    → Type (ℓ-max ℓA ℓB)
  same-parses {A = A} {B = B} p q s≡ =
    PathP (λ i → A i (s≡ i .fst) × B i (s≡ i .snd)) (p .snd) (q .snd)

  @0 ⊗PathP :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → {p : (A i0 ⊗ B i0) (w i0)}
    → {q : (A i1 ⊗ B i1) (w i1)}
    → (s≡ : same-splits {w = w} p q)
    → same-parses {A = A} {B = B} {w = w} p q s≡
    → PathP (λ i → (A i ⊗ B i) (w i)) p q
  ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

  @0 ⊗≡ : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{w}
    → (p p' : (A ⊗ B) w)
    → (s≡ : same-splits {w = λ _ → w} p p')
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
      -- Eq.J (λ u v → A u) a (Eq.sym (++-unit-r-Eq _))
      Eq.transport A (Eq.sym (++-unit-r-Eq _)) a

    ⊗-unit-r⁻ :
      A ⊢ A ⊗ ε
    ⊗-unit-r⁻ w p =
      ((w , []) , Eq.sym (++-unit-r-Eq w)) , p , ε-intro

    @0 rectify :
      ∀ {w w'}{A : Grammar ℓA}
      → {p : A w}{q : A w'}
      → {w≡ w≡' : w ≡ w'}
      → PathP (λ i → A (w≡  i)) p q
      → PathP (λ i → A (w≡' i)) p q
    rectify {w = w}{w'}{A = A}{p = p}{q = q} =
      subst {A = w ≡ w'} (λ w≡ → PathP (λ i → A (w≡ i)) p q)
        (isSetString _ _ _ _)

    ⊗-unit-l :
      ε ⊗ A ⊢ A
    ⊗-unit-l {A = A} _ ((_ , Eq.refl) , Eq.refl , a) = a

    ⊗-unit-l⁻ :
      A ⊢ ε ⊗ A
    ⊗-unit-l⁻ _ p = (_ , Eq.refl) , ε-intro , p

    @0 ⊗-unit-ll⁻ :
      ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
    ⊗-unit-ll⁻ {A = A} =
      funExt λ w → funExt λ where
        ((_ , Eq.refl) , Eq.refl , a) → refl

    @0 ⊗-unit-l⁻l :
      ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-l⁻l {A = A} = refl

    @0 cong-∘g⊗-unit-l⁻ :
      (e e' : ε ⊗ A ⊢ B) →
      (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
      e ≡ e'
    cong-∘g⊗-unit-l⁻ f A ∘g≡ =
      cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
      cong (_∘g ⊗-unit-l) ∘g≡ ∙
      cong (A ∘g_) (⊗-unit-ll⁻)

    @0 ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-rl⁻ =
      funExt λ w → funExt λ where
        Eq.refl → refl

    --technically this follows from more basic monoidal category axioms but it's not simple
    @0 ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id
    ⊗-unit-lr⁻ = funExt λ w → funExt λ where
      Eq.refl → refl

  ⊗-assoc :
    A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
  ⊗-assoc _ (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) =
    ((wa ++ wb , wc) , Eq.sym (++-assoc-Eq wa wb wc)) , ((((wa , wb) , Eq.refl) , (a , b)) , c)

  ⊗-assoc⁻ :
    (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
  ⊗-assoc⁻ _ (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) =
    ((wa , wb ++ wc) , ++-assoc-Eq wa wb wc) , (a , (((wb , wc) , Eq.refl) , (b , c)))

  @0 ⊗-assoc∘⊗-assoc⁻≡id :
   ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
  ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ where
    (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) →
      ⊗≡ _ _
        (≡-× (λ i → {!!}) {!!})
        {!!}
--     ⊗≡ _ _
--       (≡-× (λ i → p .snd .fst .fst .snd (~ i)) refl)
--       (ΣPathP (
--         (⊗PathP
--           (≡-× refl refl)
--           (≡-× refl refl)) ,
--         refl))

  @0 ⊗-assoc⁻∘⊗-assoc≡id :
   ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
  ⊗-assoc⁻∘⊗-assoc≡id = {!!}
    -- funExt λ w → funExt λ p →
    -- ⊗≡ _ _
    --   (≡-× refl (sym (p .snd .snd .fst .snd)))
    --   (ΣPathP (
    --     refl ,
    --     (⊗PathP (≡-× refl refl)
    --       (ΣPathP (refl , refl)))))

  @0 ⊗-assoc⁻⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
    ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
  ⊗-assoc⁻⊗-intro = {!!}

  @0 ⊗-assoc⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
      ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
  ⊗-assoc⊗-intro = {!!}
  -- funExt λ w → funExt λ p →
  --   ⊗≡ _ _ (≡-× refl refl) (ΣPathP (refl , refl))

  opaque
    unfolding ⊗-unit-r⁻
    @0 ⊗-assoc⁻⊗-unit-r⁻ :
      ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ =
      {!!}
    -- funExt λ w → funExt λ p →
    --   ⊗≡ _ _ (≡-× refl (++-unit-r _))
    --     (ΣPathP (refl , ⊗PathP refl refl))

  opaque
    unfolding ⊗-unit-l⁻
    ⊗-assoc⊗-unit-l⁻ :
     ⊗-assoc {A = A}{C = C} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
    ⊗-assoc⊗-unit-l⁻ = funExt λ w → funExt λ p →
      -- ⊗≡ _ _ (≡-× (++-unit-r _) refl) (ΣPathP (⊗PathP refl refl , refl))
      {!!}

  opaque
    unfolding ε ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro :
      ∀ {f : A ⊢ B}
      → ⊗-unit-l⁻ ∘g f
      ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro = refl

    ⊗-unit-l⊗-intro :
      ∀ (f : A ⊢ B)
      → f ∘g ⊗-unit-l
        ≡ ⊗-unit-l ∘g (⊗-intro id f)
    ⊗-unit-l⊗-intro f =
      {!!}
    -- cong-∘g⊗-unit-l⁻ _ _
    --     λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

    ⊗-unit-r⁻⊗-intro :
      ∀ {f : A ⊢ B}
      → ⊗-unit-r⁻ ∘g f
      ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
    ⊗-unit-r⁻⊗-intro = refl

    -- this is the fact that the inverse of a natural transformation is natural
    ⊗-unit-r⊗-intro :
      (f : A ⊢ B) →
      ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
    ⊗-unit-r⊗-intro f =
      {!!}
    -- cong-∘g⊗-unit-r⁻ _ _
    --     (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

    id,⊗id≡id : ⊗-intro id id ≡ id {A = A ⊗ B}
    id,⊗id≡id = refl

_,⊗_ = ⊗-intro
infixr 20 _,⊗_

{- ε* versions of the unitors  -}
⊗-unit*-l : ε* {ℓ} ⊗ A ⊢ A
⊗-unit*-l = ⊗-unit-l ∘g ⊗-intro lowerG id

⊗-unit*-l⁻ : A ⊢ ε* {ℓ} ⊗ A
⊗-unit*-l⁻ = ⊗-intro liftG id ∘g ⊗-unit-l⁻

opaque
  unfolding ⊗-intro
  @0 ⊗-unit*-l⊗-intro :
      ∀ (f : A ⊢ B)
      → f ∘g ⊗-unit*-l {ℓ}
        ≡ ⊗-unit*-l ∘g (⊗-intro id f)
  ⊗-unit*-l⊗-intro f =
    cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl

  @0 ⊗-unit*-ll⁻ :
    ⊗-unit*-l⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-l ≡ id
  ⊗-unit*-ll⁻ i = ⊗-intro liftG id ∘g ⊗-unit-ll⁻ i ∘g ⊗-intro lowerG id

  @0 ⊗-unit*-l⁻l :
    ⊗-unit*-l {ℓ = ℓ} {A = A} ∘g ⊗-unit*-l⁻ ≡ id
  ⊗-unit*-l⁻l = ⊗-unit-l⁻l

⊗-unit*-r : A ⊗ ε* {ℓ} ⊢ A
⊗-unit*-r = ⊗-unit-r ∘g ⊗-intro id lowerG

⊗-unit*-r⁻ : A ⊢ A ⊗ ε* {ℓ}
⊗-unit*-r⁻ = ⊗-intro id liftG ∘g ⊗-unit-r⁻

opaque
  unfolding ⊗-intro
  @0 ⊗-unit*-r⊗-intro :
      ∀ (f : A ⊢ B)
      → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
        ≡ f ∘g ⊗-unit*-r
  ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

{- Triangle -}
opaque
  unfolding ⊗-intro ⊗-unit-r ⊗-unit-l ⊗-assoc
  @0 ⊗-triangle :
    ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {A = A}{B = ε* {ℓ}}{C = B}
    ≡ ⊗-intro id ⊗-unit*-l
  ⊗-triangle {A = A}{B = B} =
    {!!}
  -- funExt λ w → funExt λ {
  --   (((w1 , w2) , w≡w1w2) ,
  --    (gp , (((w3 , w4) , w2≡w3w4) , ((lift w3≡[]) , Bp)))) →
  --   let p1 : w1 ++ w3 ≡ w1
  --       p1 = (cong (w1 ++_) w3≡[] ∙ ++-unit-r _)
  --       p2 = (cong (_++ w4) (sym w3≡[]) ∙ sym w2≡w3w4)
  --       p1' : w1 ≡ w1 ++ w3
  --       p1' = λ i → (hcomp
  --          (doubleComp-faces (λ _ → w1)
  --           (λ i₁ →
  --              hcomp (doubleComp-faces (λ _ → w1 ++ []) (λ i₂ → w1 ++ w3) i₁)
  --              (w1 ++ w3≡[] (~ i₁)))
  --           i)
  --          (++-unit-r w1 (~ i)))
  --   in
  --   ⊗≡ _ _ (≡-× p1 p2)
  --    (ΣPathP (rectify {A = A} {w≡ = sym p1'}{w≡' = p1}
  --      (symP (transport-filler (cong A p1') gp))
  --    , transport-filler (cong B p2) Bp))
  --   }

{- Pentagon -}
opaque
  unfolding ⊗-intro ⊗-assoc
  @0 ⊗-pentagon :
    ⊗-intro (⊗-assoc {A = A}) id
    ∘g ⊗-assoc
    ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D})
      ≡
    ⊗-assoc
    ∘g ⊗-assoc
  ⊗-pentagon {A = A}{B = B}{C = C}{D = D} =
    {!!}
  -- funExt λ w → funExt λ {
  --   (((w1 , w234) , w≡w1w234) , p1 ,
  --   (((w2 , w34) , w234≡w2w34) , p2 ,
  --   (((w3 , w4) , w34≡w3w4) , (p3 , p4)))) →
  --   ⊗≡ _ _
  --   (≡-× (sym (++-assoc w1 w2 w3)) refl)
  --   (ΣPathP ((⊗PathP (≡-× refl refl) refl) , refl))
  --   }

{- Big associators and big diagrams -}

@0 ⊗-assoc⁻3 :
  (A ⊗ B ⊗ C) ⊗ D ⊢ A ⊗ B ⊗ C ⊗ D
⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

@0 ⊗-assoc3 :
  A ⊗ B ⊗ C ⊗ D ⊢ (A ⊗ B ⊗ C) ⊗ D
⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

@0 ⊗-assoc⁻3⊗-unit-r⁻ :
  ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻3⊗-unit-r⁻ =
  {!!}
-- cong (id ,⊗ ⊗-assoc⁻ ∘g_) ⊗-assoc⁻⊗-unit-r⁻
--   ∙ ⊗-intro⊗-intro
--   ∙ cong (id ,⊗_) ⊗-assoc⁻⊗-unit-r⁻

@0 ⊗-assoc⁻4 :
  (A ⊗ B ⊗ C ⊗ D) ⊗ E ⊢ A ⊗ B ⊗ C ⊗ D ⊗ E
⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

@0 ⊗-assoc4 :
  A ⊗ B ⊗ C ⊗ D ⊗ E ⊢ (A ⊗ B ⊗ C ⊗ D) ⊗ E
⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3

@0 ⊗-assoc⁻4⊗-unit-r⁻ :
  ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻4⊗-unit-r⁻ =
  {!!}
-- cong (id ,⊗ ⊗-assoc⁻3 ∘g_) ⊗-assoc⁻⊗-unit-r⁻
--   ∙ ⊗-intro⊗-intro
--   ∙ cong (id ,⊗_) ⊗-assoc⁻3⊗-unit-r⁻

opaque
  unfolding ⊗-intro ⊗-assoc
  @0 ⊗-assoc⁻4⊗-intro :
    ∀ {f f' f'' f''' f''''} →
    (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
  ⊗-assoc⁻4⊗-intro = {!!} -- refl

opaque
  unfolding ⊗-intro ⊗-assoc
  @0 ⊗-assoc3⊗-assoc⁻3 : ⊗-assoc3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc⁻3 ≡ id
  ⊗-assoc3⊗-assoc⁻3 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc∘⊗-assoc⁻≡id i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
    ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩ id ∎

  @0 ⊗-assoc4⊗-assoc⁻4 : ⊗-assoc4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g ⊗-assoc⁻4 ≡ id
  ⊗-assoc4⊗-assoc⁻4 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc3 ∘g id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc3⊗-assoc⁻3 i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
      ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
    id ∎

  @0 ⊗-assoc⁻3⊗-assoc3 : ⊗-assoc⁻3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc3 ≡ id
  ⊗-assoc⁻3⊗-assoc3 =
    id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc) ⟩
    id ,⊗ (⊗-assoc⁻ ∘g ⊗-assoc) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻∘⊗-assoc≡id i)) ⟩
    id ∎

  @0 ⊗-assoc⁻4⊗-assoc4 : ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E}∘g ⊗-assoc4 ≡ id
  ⊗-assoc⁻4⊗-assoc4 =
    id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc3
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc3) ⟩
    id ,⊗ (⊗-assoc⁻3 ∘g ⊗-assoc3) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻3⊗-assoc3 i)) ⟩
    id ∎

  @0 ⊗-assoc4⊗-intro :
    ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
  ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
    {!!}
  -- sym (invMoveR {f = ⊗-assoc⁻4} {f⁻ = ⊗-assoc4} ⊗-assoc4⊗-assoc⁻4
  --     (cong ((f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''') ∘g_) ⊗-assoc⁻4⊗-assoc4))

open StrongEquivalence
module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  {C : Grammar ℓC} {D : Grammar ℓD}
  (A≅B : A ≅ B)
  (C≅D : C ≅ D)
  where

  private
    the-fun : A ⊗ C ⊢ B ⊗ D
    the-fun = A≅B .fun ,⊗ C≅D .fun

    the-inv : B ⊗ D ⊢ A ⊗ C
    the-inv = A≅B .inv ,⊗ C≅D .inv
    opaque
      unfolding ⊗-intro
      @0 the-sec : the-fun ∘g the-inv ≡ id
      the-sec i = A≅B .sec i ,⊗ C≅D .sec i

      @0 the-ret : the-inv ∘g the-fun ≡ id
      the-ret i = A≅B .ret i ,⊗ C≅D .ret i

  ⊗≅ : (A ⊗ C) ≅ (B ⊗ D)
  ⊗≅ .fun = the-fun
  ⊗≅ .inv = the-inv
  ⊗≅ .sec = the-sec
  ⊗≅ .ret = the-ret

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  where
  ⊗-assoc≅ : A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C
  ⊗-assoc≅ .fun = ⊗-assoc
  ⊗-assoc≅ .inv = ⊗-assoc⁻
  ⊗-assoc≅ .sec = ⊗-assoc∘⊗-assoc⁻≡id
  ⊗-assoc≅ .ret = ⊗-assoc⁻∘⊗-assoc≡id
