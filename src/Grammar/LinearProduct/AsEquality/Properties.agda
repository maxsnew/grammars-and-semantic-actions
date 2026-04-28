open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

module Grammar.LinearProduct.AsEquality.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Equality as Eq
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet
  hiding (Splitting
        ; isSetSplitting
        ; SplittingPathP
        ; Splitting≡
        ; splitting++)
  renaming (SplittingEq to Splitting
          ; isSetSplittingEq to isSetSplitting
          ; SplittingEqPathP to SplittingPathP
          ; SplittingEq≡ to Splitting≡
          ; leftEq to left
          ; rightEq to right
          ; splittingEq++ to splitting++)
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
import Grammar.Epsilon.AsEquality.Base Alphabet as εEq
import Grammar.Epsilon.AsEquality.Properties Alphabet as εEqP
import Grammar.Epsilon.AsPath.Base Alphabet as εPath
open import Grammar.LinearProduct.AsEquality.Base Alphabet
import Grammar.LinearProduct.AsPath.Base Alphabet as ⊗Path
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

-- Bridge between the path-flavored ⊗ and the equality-flavored ⊗.
-- Since Splitting≡SplittingEq holds pointwise, the underlying Σ-types
-- of the two ⊗s are propositionally equal as Grammars.
opaque
  unfolding _⊗_ ⊗Path._⊗_

  ⊗Path≡⊗Eq : A ⊗Path.⊗ B ≡ A ⊗ B
  ⊗Path≡⊗Eq {A = A} {B = B} =
    funExt λ w i →
      Σ[ s ∈ Splitting≡SplittingEq w i ] A (s .fst .fst) × B (s .fst .snd)

  isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  isSetGrammar⊗ isSetA isSetB =
    subst isSetGrammar ⊗Path≡⊗Eq (⊗Path.isSetGrammar⊗ isSetA isSetB)

  has-split :
    ∀ (w : String) → (p : (A ⊗ B) w) → (s : Splitting w) → Type ℓ-zero
  has-split w p s = s ≡ p .fst

  isProp-has-split :
    ∀ (w : String) (p : (A ⊗ B) w) (s : Splitting w)
    → isProp (has-split w p s)
  isProp-has-split w p s = isSetSplitting w _ _

  the-split :
    ∀ (w : String) → (p : (A ⊗ B) w) → Σ[ s ∈ Splitting w ] has-split w p s
  the-split w p = (p .fst) , refl

same-splits :
  {A : Grammar ℓA} {B : Grammar ℓB}
  {C : Grammar ℓC} {D : Grammar ℓD}
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

  ⊗PathP :
    {A : I → Grammar ℓA}{B : I → Grammar ℓB}
    {w : I → String}
    → {p : (A i0 ⊗ B i0) (w i0)}
    → {q : (A i1 ⊗ B i1) (w i1)}
    → (s≡ : same-splits {w = w} p q)
    → same-parses {A = A} {B = B} {w = w} p q s≡
    → PathP (λ i → (A i ⊗ B i) (w i)) p q
  ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

  ⊗≡ : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{w}
    → (p p' : (A ⊗ B) w)
    → (s≡ : same-splits {w = λ _ → w} p p')
    → same-parses {A = λ _ → A} {B = λ _ → B} {w = λ _ → w} p p' s≡
    → p ≡ p'
  ⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡

opaque
  unfolding _⊗_ ⊗-intro εEq.ε εEq.ε-intro ⊗-unit-l ⊗-unit-l⁻ ⊗-unit-r ⊗-unit-r⁻ ⊗-assoc ⊗-assoc⁻

  ⊗-intro⊗-intro
    : ∀ {f : A ⊢ B}{f' : C ⊢ D}
        {f'' : E ⊢ A}
        {f''' : F ⊢ C}
    → ⊗-intro f f' ∘g ⊗-intro f'' f'''
      ≡ ⊗-intro (f ∘g f'') (f' ∘g f''')
  ⊗-intro⊗-intro = refl

  id,⊗id≡id : ⊗-intro id id ≡ id {A = A ⊗ B}
  id,⊗id≡id = refl

  ⊗-unit-l⁻⊗-intro :
    ∀ {f : A ⊢ B}
    → ⊗-unit-l⁻ ∘g f ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
  ⊗-unit-l⁻⊗-intro = refl

  ⊗-unit-r⁻⊗-intro :
    ∀ {f : A ⊢ B}
    → ⊗-unit-r⁻ ∘g f ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
  ⊗-unit-r⁻⊗-intro = refl

  ⊗-assoc⁻⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
    ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
  ⊗-assoc⁻⊗-intro = funExt λ w → funExt λ where
    (((_ , _) , Eq.refl) , (((_ , _) , Eq.refl) , _ , _) , _) → refl

  ⊗-assoc⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
      ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
  ⊗-assoc⊗-intro = funExt λ w → funExt λ where
    (((_ , _) , Eq.refl) , _ , ((_ , _) , Eq.refl) , _ , _) → refl

  -- Helper: relate Eq.transport to PathP along Eq.eqToPath
  Eq-transp-path : ∀ {ℓX ℓY} {X : Type ℓX} (Y : X → Type ℓY)
    → {x y : X} (p : x Eq.≡ y) (b : Y x)
    → PathP (λ i → Y (Eq.eqToPath p i)) b (Eq.transport Y p b)
  Eq-transp-path Y Eq.refl b = refl

  rectify : ∀ {w w' : String} {A : Grammar ℓA}
    → {p : A w}{q : A w'}
    → {w≡ w≡' : w ≡ w'}
    → PathP (λ i → A (w≡  i)) p q
    → PathP (λ i → A (w≡' i)) p q
  rectify {A = A}{p = p}{q = q} =
    subst (λ w≡ → PathP (λ i → A (w≡ i)) p q) (isSetString _ _ _ _)

  ⊗-unit-rr⁻ : ∀ {A : Grammar ℓA}
    → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
  ⊗-unit-rr⁻ {A = A} = funExt λ w → funExt λ where
    ((_ , Eq.refl) , a , Eq.refl) →
      ΣPathP
        ( ΣPathP
          ( ≡-× (Eq.eqToPath (++-unit-r-Eq _)) refl
          , isProp→PathP (λ _ → isSetEqString _ _) _ _)
        , ΣPathP
          ( rectify {A = A} (symP (Eq-transp-path A _ a))
          , refl))

  -- Transport along a propositional loop equality is the identity
  Eq-transport-loop : ∀ {ℓA} {A : Grammar ℓA} {w : String}
    → (p : w Eq.≡ w) (a : A w)
    → Eq.transport A p a ≡ a
  Eq-transport-loop {A = A} p a =
    cong (λ q → Eq.transport A q a) (isSetEqString _ _ p Eq.refl)

  ⊗-unit-r⁻r : ∀ {A : Grammar ℓA}
    → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
  ⊗-unit-r⁻r {A = A} = funExt λ w → funExt λ a → Eq-transport-loop _ a

  ⊗-unit-ll⁻ : ∀ {A : Grammar ℓA}
    → ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
  ⊗-unit-ll⁻ {A = A} = funExt λ w → funExt λ where
    ((_ , Eq.refl) , Eq.refl , a) →
      ΣPathP
        ( ΣPathP
          ( ≡-× refl refl
          , isProp→PathP (λ _ → isSetEqString _ _) _ _)
        , ΣPathP
          ( isProp→PathP (λ _ → isSetEqString _ _) _ _
          , refl))

  ⊗-unit-l⁻l : ∀ {A : Grammar ℓA}
    → ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id
  ⊗-unit-l⁻l {A = A} = funExt λ w → funExt λ a → refl

  cong-∘g⊗-unit-l⁻ :
    (e e' : εEq.ε ⊗ A ⊢ B) →
    (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
    e ≡ e'
  cong-∘g⊗-unit-l⁻ f g ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
    cong (_∘g ⊗-unit-l) ∘g≡ ∙
    cong (g ∘g_) ⊗-unit-ll⁻

  cong-∘g⊗-unit-r⁻ :
    (e e' : A ⊗ εEq.ε ⊢ B) →
    (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
    e ≡ e'
  cong-∘g⊗-unit-r⁻ f g ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
    cong (_∘g ⊗-unit-r) ∘g≡ ∙
    cong (g ∘g_) ⊗-unit-rr⁻

  ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
  ⊗-unit-rl⁻ = funExt λ w → funExt λ p →
    εEqP.isLangε w ((⊗-unit-r ∘g ⊗-unit-l⁻) w p) (id {A = εEq.ε} w p)

  ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id
  ⊗-unit-lr⁻ = funExt λ w → funExt λ p →
    εEqP.isLangε w ((⊗-unit-l ∘g ⊗-unit-r⁻) w p) (id {A = εEq.ε} w p)

  ⊗-assoc∘⊗-assoc⁻≡id :
    ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
  ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ where
    (((_ , _) , Eq.refl) , (((_ , _) , Eq.refl) , a , b) , c) →
      ΣPathP
        ( ΣPathP
          ( ≡-× refl refl
          , isProp→PathP (λ _ → isSetEqString _ _) _ _)
        , ΣPathP
          ( ΣPathP
            ( ΣPathP
              ( ≡-× refl refl
              , isProp→PathP (λ _ → isSetEqString _ _) _ _)
            , ΣPathP (refl , refl))
          , refl))

  ⊗-assoc⁻∘⊗-assoc≡id :
    ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
  ⊗-assoc⁻∘⊗-assoc≡id = funExt λ w → funExt λ where
    (((_ , _) , Eq.refl) , a , (((_ , _) , Eq.refl) , b , c)) →
      ΣPathP
        ( ΣPathP
          ( ≡-× refl refl
          , isProp→PathP (λ _ → isSetEqString _ _) _ _)
        , ΣPathP
          ( refl
          , ΣPathP
            ( ΣPathP
              ( ≡-× refl refl
              , isProp→PathP (λ _ → isSetEqString _ _) _ _)
            , ΣPathP (refl , refl))))

  opaque
    unfolding ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ :
      ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ {A = A} {B = B} = funExt λ w → funExt λ where
      (((_ , _) , Eq.refl) , a , b) →
        ΣPathP
          ( ΣPathP
            ( ≡-× refl (Eq.eqToPath (++-unit-r-Eq _))
            , isProp→PathP (λ _ → isSetEqString _ _) _ _)
          , ΣPathP
            ( refl
            , ΣPathP
              ( ΣPathP
                ( ≡-× refl refl
                , isProp→PathP (λ _ → isSetEqString _ _) _ _)
              , ΣPathP (refl , refl))))

  opaque
    unfolding ⊗-unit-l⁻
    ⊗-assoc⊗-unit-l⁻ :
      ⊗-assoc {A = A}{C = C} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
    ⊗-assoc⊗-unit-l⁻ {A = A}{C = C} = funExt λ w → funExt λ where
      (((_ , _) , Eq.refl) , a , c) →
        ΣPathP
          ( ΣPathP
            ( ≡-× (Eq.eqToPath (++-unit-r-Eq _)) refl
            , isProp→PathP (λ _ → isSetEqString _ _) _ _)
          , ΣPathP
            ( ΣPathP
              ( ΣPathP
                ( ≡-× refl refl
                , isProp→PathP (λ _ → isSetEqString _ _) _ _)
              , ΣPathP (refl , refl))
            , refl))

  ⊗-unit-l⊗-intro :
    ∀ (f : A ⊢ B)
    → f ∘g ⊗-unit-l
      ≡ ⊗-unit-l ∘g (⊗-intro id f)
  ⊗-unit-l⊗-intro f =
    cong-∘g⊗-unit-l⁻ _ _
      λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

  ⊗-unit-r⊗-intro :
    (f : A ⊢ B) →
    ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
  ⊗-unit-r⊗-intro f =
    cong-∘g⊗-unit-r⁻ _ _
      (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

  ⊗-unit*-l⊗-intro :
    ∀ (f : A ⊢ B)
    → f ∘g ⊗-unit*-l {ℓ}
      ≡ ⊗-unit*-l ∘g (⊗-intro id f)
  ⊗-unit*-l⊗-intro f i = ⊗-unit-l⊗-intro f i ∘g ⊗-intro lowerG id

  ⊗-unit*-ll⁻ :
    ⊗-unit*-l⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-l ≡ id
  ⊗-unit*-ll⁻ i = ⊗-intro liftG id ∘g ⊗-unit-ll⁻ i ∘g ⊗-intro lowerG id

  ⊗-unit*-l⁻l :
    ⊗-unit*-l {ℓ = ℓ} {A = A} ∘g ⊗-unit*-l⁻ ≡ id
  ⊗-unit*-l⁻l = ⊗-unit-l⁻l

  ⊗-unit*-r⊗-intro :
    ∀ (f : A ⊢ B)
    → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
      ≡ f ∘g ⊗-unit*-r
  ⊗-unit*-r⊗-intro {ℓ = ℓ} f i =
    ⊗-unit-r⊗-intro f i ∘g ⊗-intro id lowerG

  ⊗-unit*-rr⁻ :
    ⊗-unit*-r⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r ≡ id
  ⊗-unit*-rr⁻ {A = A} {ℓ = ℓ} i =
    ⊗-intro id liftG ∘g ⊗-unit-rr⁻ {A = A} i ∘g ⊗-intro id lowerG

  ⊗-unit*-r⁻r :
    ⊗-unit*-r {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r⁻ ≡ id
  ⊗-unit*-r⁻r = ⊗-unit-r⁻r

{- Big associators and big diagrams -}

opaque
  unfolding _⊗_ ⊗-intro ⊗-assoc ⊗-assoc⁻ ⊗-unit-r ⊗-unit-r⁻

  ⊗-assoc⁻3⊗-unit-r⁻ :
    ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
    ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
  ⊗-assoc⁻3⊗-unit-r⁻ =
    cong (id ,⊗ ⊗-assoc⁻ ∘g_) ⊗-assoc⁻⊗-unit-r⁻
    ∙ ⊗-intro⊗-intro {f = id} {f' = ⊗-assoc⁻} {f'' = id} {f''' = ⊗-unit-r⁻}
    ∙ cong (id ,⊗_) ⊗-assoc⁻⊗-unit-r⁻

  ⊗-assoc⁻4⊗-unit-r⁻ :
    ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-unit-r⁻
    ≡ id ,⊗ id ,⊗ id ,⊗ ⊗-unit-r⁻
  ⊗-assoc⁻4⊗-unit-r⁻ {A = A}{B = B}{C = C}{D = D} =
    cong (id ,⊗ ⊗-assoc⁻3 ∘g_) ⊗-assoc⁻⊗-unit-r⁻
    ∙ ⊗-intro⊗-intro {f = id} {f' = ⊗-assoc⁻3} {f'' = id} {f''' = ⊗-unit-r⁻}
    ∙ (λ i → ⊗-intro (id {A = A}) (⊗-assoc⁻3⊗-unit-r⁻ {A = B}{B = C}{C = D} i))

  ⊗-assoc⁻4⊗-intro :
    ∀ {f f' f'' f''' f''''} →
    (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E}
      ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
        ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
  ⊗-assoc⁻4⊗-intro = funExt λ w → funExt λ where
    (((_ , _) , Eq.refl)
      , (((_ , _) , Eq.refl) , a
         , (((_ , _) , Eq.refl) , b
            , (((_ , _) , Eq.refl) , c , d))) , e)
      → refl

  ⊗-assoc3⊗-assoc⁻3 :
    ⊗-assoc3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc⁻3 ≡ id
  ⊗-assoc3⊗-assoc⁻3 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc∘⊗-assoc⁻≡id i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
      ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
    id ∎

  ⊗-assoc4⊗-assoc⁻4 :
    ⊗-assoc4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g ⊗-assoc⁻4 ≡ id
  ⊗-assoc4⊗-assoc⁻4 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc3 ∘g id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc3⊗-assoc⁻3 i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
      ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
    id ∎

  ⊗-assoc⁻3⊗-assoc3 :
    ⊗-assoc⁻3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc3 ≡ id
  ⊗-assoc⁻3⊗-assoc3 =
    id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc) ⟩
    id ,⊗ (⊗-assoc⁻ ∘g ⊗-assoc)
      ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻∘⊗-assoc≡id i)) ⟩
    id ∎

  ⊗-assoc⁻4⊗-assoc4 :
    ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g ⊗-assoc4 ≡ id
  ⊗-assoc⁻4⊗-assoc4 =
    id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc3
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc3) ⟩
    id ,⊗ (⊗-assoc⁻3 ∘g ⊗-assoc3)
      ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻3⊗-assoc3 i)) ⟩
    id ∎

  ⊗-assoc4⊗-intro :
    ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
  ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
    sym (invMoveR {f = ⊗-assoc⁻4} {f⁻ = ⊗-assoc4} ⊗-assoc4⊗-assoc⁻4
      (cong ((f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''') ∘g_) ⊗-assoc⁻4⊗-assoc4))

{- Triangle and pentagon -}
opaque
  unfolding _⊗_ ⊗-intro ⊗-assoc εEq.ε εEq.ε-intro ⊗-unit-r ⊗-unit-l
            same-parses ⊗PathP ⊗≡ the-split

  ⊗-triangle :
    ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {A = A}{B = εEq.ε* {ℓ}}{C = B}
    ≡ ⊗-intro id ⊗-unit*-l
  ⊗-triangle {A = A}{B = B} = funExt λ w → funExt λ where
    (((wa , _) , Eq.refl)
      , a , (((_ , wc) , Eq.refl) , (lift Eq.refl) , b)) →
      ⊗≡ _ _ (≡-× (++-unit-r wa) refl)
        (ΣPathP
          ( rectify {A = A}
              (symP (Eq-transp-path A
                (Eq.sym (++-unit-r-Eq wa) Eq.∙ Eq.refl) a))
          , refl))

  ⊗-pentagon :
    ⊗-intro (⊗-assoc {A = A}) id
    ∘g ⊗-assoc
    ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D})
      ≡
    ⊗-assoc
    ∘g ⊗-assoc
  ⊗-pentagon {A = A}{B = B}{C = C}{D = D} = funExt λ w → funExt λ where
    (((w1 , _) , Eq.refl)
      , p1 , (((w2 , _) , Eq.refl)
          , p2 , (((w3 , _) , Eq.refl) , p3 , p4))) →
      ⊗≡ _ _
        (≡-× (sym (++-assoc w1 w2 w3)) refl)
        (ΣPathP ((⊗PathP (≡-× refl refl) refl) , refl))

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
      unfolding _⊗_ ⊗-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec i = A≅B .sec i ,⊗ C≅D .sec i

      the-ret : the-inv ∘g the-fun ≡ id
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

εr≅ : A ≅ A ⊗ εEq.ε
εr≅ .fun = ⊗-unit-r⁻
εr≅ .inv = ⊗-unit-r
εr≅ .sec = ⊗-unit-rr⁻
εr≅ .ret = ⊗-unit-r⁻r

εl≅ : A ≅ εEq.ε ⊗ A
εl≅ .fun = ⊗-unit-l⁻
εl≅ .inv = ⊗-unit-l
εl≅ .sec = ⊗-unit-ll⁻
εl≅ .ret = ⊗-unit-l⁻l
