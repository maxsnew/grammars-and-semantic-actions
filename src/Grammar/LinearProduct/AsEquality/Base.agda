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
      Eq.transport A (Eq.sym (++-unit-r-Eq _)) a

    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
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

    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l {A = A} _ ((_ , Eq.refl) , Eq.refl , a) = a

    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    ⊗-unit-l⁻ _ p = (_ , Eq.refl) , ε-intro , p

    @0 ⊗-unit-ll⁻ : ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
    ⊗-unit-ll⁻ {A = A} = funExt λ w → funExt λ where
        ((_ , Eq.refl) , Eq.refl , a) → refl

    @0 ⊗-unit-l⁻l : ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id
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

  ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
  ⊗-assoc _ (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) =
    ((wa ++ wb , wc) , Eq.sym (++-assoc-Eq wa wb wc)) , ((((wa , wb) , Eq.refl) , (a , b)) , c)

  ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
  ⊗-assoc⁻ _ (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) =
    ((wa , wb ++ wc) , ++-assoc-Eq wa wb wc) , (a , (((wb , wc) , Eq.refl) , (b , c)))

  opaque
    unfolding ε ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro : ∀ {f : A ⊢ B} → ⊗-unit-l⁻ ∘g f ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro = refl

    ⊗-unit-r⁻⊗-intro : ∀ {f : A ⊢ B} → ⊗-unit-r⁻ ∘g f ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
    ⊗-unit-r⁻⊗-intro = refl

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

{- Big associators and big diagrams -}

@0 ⊗-assoc⁻3 :
  (A ⊗ B ⊗ C) ⊗ D ⊢ A ⊗ B ⊗ C ⊗ D
⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

@0 ⊗-assoc3 :
  A ⊗ B ⊗ C ⊗ D ⊢ (A ⊗ B ⊗ C) ⊗ D
⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

@0 ⊗-assoc⁻4 :
  (A ⊗ B ⊗ C ⊗ D) ⊗ E ⊢ A ⊗ B ⊗ C ⊗ D ⊗ E
⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

@0 ⊗-assoc4 :
  A ⊗ B ⊗ C ⊗ D ⊗ E ⊢ (A ⊗ B ⊗ C ⊗ D) ⊗ E
⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3

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
