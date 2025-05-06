{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lower)
open import Cubical.Foundations.HLevels

module @0 Grammar.LinearProduct.AsPath.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Erased.Data.List
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Epsilon.AsPath Alphabet isSetAlphabet
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

opaque
  unfolding _⊗_
  isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)
  isSetGrammar⊗ isSetG isSetB w = isSetΣ (isSetSplitting w)
    λ _ → isSet× (isSetG _) (isSetB _)

opaque
  unfolding _⊗_
  -- because ⊗ is opaque,
  -- same-splits and same-parses are needed so that the interface of
  -- ⊗ doesn't leak in the type signature of ⊗PathP
  has-split :
    ∀ (w : String) → (p : (A ⊗ B) w) → (s : Splitting w) → Type ℓ-zero
  has-split w p s = s ≡ p .fst

  isProp-has-split : ∀ (w : String) (p : (A ⊗ B) w) → (s : Splitting w) → isProp (has-split w p s)
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
  unfolding _⊗_
  rectify :
    ∀ {w w'}{A : Grammar ℓA}
    → {p : A w}{q : A w'}
    → {w≡ w≡' : w ≡ w'}
    → PathP (λ i → A (w≡  i)) p q
    → PathP (λ i → A (w≡' i)) p q
  rectify {w = w}{w'}{A = A}{p = p}{q = q} =
    subst {A = w ≡ w'} (λ w≡ → PathP (λ i → A (w≡ i)) p q)
      (isSetString _ _ _ _)

  ⊗-intro⊗-intro : ∀ {f : A ⊢ B}{f' : C ⊢ D} {f'' : E ⊢ A} {f''' : F ⊢ C}
    → f ,⊗ f' ∘g f'' ,⊗ f''' ≡ (f ∘g f'') ,⊗ (f' ∘g f''')
  ⊗-intro⊗-intro = refl

  opaque
    unfolding ⊗-unit-r the-split ⊗≡ ε
    ⊗-unit-rr⁻ :
      ∀ {A : Grammar ℓA}
      → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
    ⊗-unit-rr⁻ {A = A} =
      funExt λ w → funExt λ (s , a , eps) →
      let w≡w' = w≡l++r s ∙ cong (left s ++_) eps ∙ ++-unit-r _
      in
      ⊗≡ _ _
        (≡-× w≡w' (sym eps))
        (ΣPathP (
          symP (subst-filler A (sym w≡w') a) ,
          (isProp→PathP (λ _ → isLangε _) _ _)))

    ⊗-unit-r⁻r : ∀ {A : Grammar ℓA}
      → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
    ⊗-unit-r⁻r {A = A} = funExt λ w → funExt λ a →
      subst (λ w≡w' → subst A w≡w' a ≡ a)
        (isSetString _ _ _ _) (substRefl {B = A} a)

  opaque
    unfolding ⊗-unit-l the-split ⊗≡ ε
    ⊗-unit-ll⁻ : ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
    ⊗-unit-ll⁻ {A = A} =
      funExt λ w → funExt λ (s , eps , a) →
      let w'≡w = sym (w≡l++r s ∙ cong (_++ right s) eps)
      in
      ⊗≡ _ _ (≡-× (sym eps) (sym w'≡w))
       (ΣPathP ((isProp→PathP (λ _ → isLangε _) _ _) ,
         symP (subst-filler A w'≡w a)))

    ⊗-unit-l⁻l : ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-l⁻l {A = A} = funExt λ w → funExt λ a →
      subst (λ w'≡w → subst A w'≡w a ≡ a)
        (isSetString _ _ _ _) (substRefl {B = A} a)

cong-∘g⊗-unit-l⁻ :
  (e e' : ε ⊗ A ⊢ B) →
  (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
  e ≡ e'
cong-∘g⊗-unit-l⁻ f A ∘g≡ =
  cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
  cong (_∘g ⊗-unit-l) ∘g≡ ∙
  cong (A ∘g_) (⊗-unit-ll⁻)

cong-∘g⊗-unit-r⁻ :
  (e e' : A ⊗ ε ⊢ B) →
  (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
  e ≡ e'
cong-∘g⊗-unit-r⁻ {A = A} f f' ∘g≡ =
  cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
  cong (_∘g ⊗-unit-r) ∘g≡ ∙
  cong (f' ∘g_) (⊗-unit-rr⁻)

opaque
  unfolding ⊗-unit-r ⊗-unit-l⁻
  ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
  ⊗-unit-rl⁻ = funExt λ w → funExt λ p →
    isSetString w [] ((⊗-unit-r ∘g ⊗-unit-l⁻) w p) (id {A = ε} w p)

  --technically this follows from more basic monoidal category axioms but it's not simple
  ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id
  ⊗-unit-lr⁻ = funExt λ w → funExt λ p →
    isSetString w [] ((⊗-unit-l ∘g ⊗-unit-r⁻ ) w p) ((id {A = ε} w p))

opaque
  unfolding _⊗_ ⊗-assoc ⊗≡
  ⊗-assoc∘⊗-assoc⁻≡id : ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
  ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ p →
    ⊗≡ _ _
      (≡-× (λ i → p .snd .fst .fst .snd (~ i)) refl)
      (ΣPathP (
        (⊗PathP
          (≡-× refl refl)
          (≡-× refl refl)) ,
        refl))

  ⊗-assoc⁻∘⊗-assoc≡id : ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
  ⊗-assoc⁻∘⊗-assoc≡id = funExt λ w → funExt λ p →
    ⊗≡ _ _
      (≡-× refl (sym (p .snd .snd .fst .snd)))
      (ΣPathP (
        refl ,
        (⊗PathP (≡-× refl refl)
          (ΣPathP (refl , refl)))))

  ⊗-assoc⁻⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
    ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
  ⊗-assoc⁻⊗-intro = refl

  ⊗-assoc⊗-intro :
    ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
    → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
      ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
  ⊗-assoc⊗-intro = refl

  opaque
    unfolding ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ :
      ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ = funExt λ w → funExt λ p →
      ⊗≡ _ _ (≡-× refl (++-unit-r _))
        (ΣPathP (refl , ⊗PathP refl refl))

  opaque
    unfolding ⊗-unit-l⁻ ⊗-unit-r⁻
    ⊗-assoc⊗-unit-l⁻ :
     ⊗-assoc {A = A}{C = C} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
    ⊗-assoc⊗-unit-l⁻ = funExt λ w → funExt λ p →
      ⊗≡ _ _ (≡-× (++-unit-r _) refl) (ΣPathP (⊗PathP refl refl , refl))

  opaque
    unfolding ε ⊗-unit-l⁻ ⊗-unit-r⁻
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
      cong-∘g⊗-unit-l⁻ _ _
        λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

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
      cong-∘g⊗-unit-r⁻ _ _
        (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

    id,⊗id≡id : ⊗-intro id id ≡ id {A = A ⊗ B}
    id,⊗id≡id = refl

opaque
  unfolding ⊗-intro
  ⊗-unit*-l⊗-intro :
      ∀ (f : A ⊢ B)
      → f ∘g ⊗-unit*-l {ℓ}
        ≡ ⊗-unit*-l ∘g (⊗-intro id f)
  ⊗-unit*-l⊗-intro f =
    cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl
  ⊗-unit*-ll⁻ :
    ⊗-unit*-l⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-l ≡ id
  ⊗-unit*-ll⁻ i = ⊗-intro liftG id ∘g ⊗-unit-ll⁻ i ∘g ⊗-intro lowerG id

  ⊗-unit*-l⁻l :
    ⊗-unit*-l {ℓ = ℓ} {A = A} ∘g ⊗-unit*-l⁻ ≡ id
  ⊗-unit*-l⁻l = ⊗-unit-l⁻l

opaque
  unfolding ⊗-intro
  ⊗-unit*-r⊗-intro :
      ∀ (f : A ⊢ B)
      → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
        ≡ f ∘g ⊗-unit*-r
  ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

  ⊗-unit*-rr⁻ :
    ⊗-unit*-r⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r ≡ id
  ⊗-unit*-rr⁻ {A = A} {ℓ = ℓ} i = ⊗-intro id liftG ∘g ⊗-unit-rr⁻ {A = A} i ∘g ⊗-intro id lowerG

  ⊗-unit*-r⁻r :
    ⊗-unit*-r {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r⁻ ≡ id
  ⊗-unit*-r⁻r = ⊗-unit-r⁻r

{- Triangle -}
opaque
  unfolding ⊗-intro ⊗-unit-r ⊗-unit-l ⊗-assoc ⊗≡ rectify ε
  ⊗-triangle :
    ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {A = A}{B = ε* {ℓ}}{C = B}
    ≡ ⊗-intro id ⊗-unit*-l
  ⊗-triangle {A = A} {B = B} = funExt λ w → funExt λ where
    (s , a , (s' , lift eps , b)) →
      let wa++wε≡wa : left s ++ left s' ≡ left s
          wa++wε≡wa = cong (_ ++_) eps ∙ ++-unit-r _
          r'≡r : right s' ≡ right s
          r'≡r = _ -- cong (_++ _) (sym eps) ∙ sym (w≡l++r s')
          wa++wε≡wa' : left s ≡ left s ++ left s'
          wa++wε≡wa' = _
      in
      ⊗≡ _ _ (≡-× wa++wε≡wa r'≡r)
        (ΣPathP (rectify {A = A} {w≡ = sym wa++wε≡wa'} {w≡' = wa++wε≡wa}
          (symP (transport-filler (cong A wa++wε≡wa') a)) ,
          transport-filler (cong B r'≡r) b))

{- Pentagon -}
opaque
  unfolding ⊗-intro ⊗-assoc ⊗≡
  ⊗-pentagon :
    ⊗-intro (⊗-assoc {A = A}) id
    ∘g ⊗-assoc
    ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D})
      ≡
    ⊗-assoc
    ∘g ⊗-assoc
  ⊗-pentagon {A = A}{B = B}{C = C}{D = D} =
    funExt λ w → funExt λ {
    (((w1 , w234) , w≡w1w234) , p1 ,
    (((w2 , w34) , w234≡w2w34) , p2 ,
    (((w3 , w4) , w34≡w3w4) , (p3 , p4)))) →
    ⊗≡ _ _
    (≡-× (sym (++-assoc w1 w2 w3)) refl)
    (ΣPathP ((⊗PathP (≡-× refl refl) refl) , refl))
    }

⊗-assoc⁻3⊗-unit-r⁻ :
  ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻3⊗-unit-r⁻ =
  cong (id ,⊗ ⊗-assoc⁻ ∘g_) ⊗-assoc⁻⊗-unit-r⁻
  ∙ ⊗-intro⊗-intro
  ∙ cong (id ,⊗_) ⊗-assoc⁻⊗-unit-r⁻

⊗-assoc⁻4⊗-unit-r⁻ :
  ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻4⊗-unit-r⁻ =
  cong (id ,⊗ ⊗-assoc⁻3 ∘g_) ⊗-assoc⁻⊗-unit-r⁻
  ∙ ⊗-intro⊗-intro
  ∙ cong (id ,⊗_) ⊗-assoc⁻3⊗-unit-r⁻

opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-assoc⁻4⊗-intro :
    ∀ {f f' f'' f''' f''''} →
    (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
  ⊗-assoc⁻4⊗-intro = refl

opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-assoc3⊗-assoc⁻3 : ⊗-assoc3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc⁻3 ≡ id
  ⊗-assoc3⊗-assoc⁻3 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc∘⊗-assoc⁻≡id i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
    ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩ id ∎

  ⊗-assoc4⊗-assoc⁻4 : ⊗-assoc4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g ⊗-assoc⁻4 ≡ id
  ⊗-assoc4⊗-assoc⁻4 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc3 ∘g id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc3⊗-assoc⁻3 i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
      ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
    id ∎

  ⊗-assoc⁻3⊗-assoc3 : ⊗-assoc⁻3 {A = A}{B = B}{C = C}{D = D} ∘g ⊗-assoc3 ≡ id
  ⊗-assoc⁻3⊗-assoc3 =
    id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc) ⟩
    id ,⊗ (⊗-assoc⁻ ∘g ⊗-assoc) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻∘⊗-assoc≡id i)) ⟩
    id ∎

  ⊗-assoc⁻4⊗-assoc4 : ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E}∘g ⊗-assoc4 ≡ id
  ⊗-assoc⁻4⊗-assoc4 =
    id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc3
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc3) ⟩
    id ,⊗ (⊗-assoc⁻3 ∘g ⊗-assoc3) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻3⊗-assoc3 i)) ⟩
    id ∎

  ⊗-assoc4⊗-intro :
    ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
  ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
    sym (invMoveR {f = ⊗-assoc⁻4} {f⁻ = ⊗-assoc4} ⊗-assoc4⊗-assoc⁻4
      (cong ((f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''') ∘g_) ⊗-assoc⁻4⊗-assoc4))

open StrongEquivalence

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

εr≅ : A ≅ A ⊗ ε
εr≅ .fun = ⊗-unit-r⁻
εr≅ .inv = ⊗-unit-r
εr≅ .sec = ⊗-unit-rr⁻
εr≅ .ret = ⊗-unit-r⁻r

εl≅ : A ≅ ε ⊗ A
εl≅ .fun = ⊗-unit-l⁻
εl≅ .inv = ⊗-unit-l
εl≅ .sec = ⊗-unit-ll⁻
εl≅ .ret = ⊗-unit-l⁻l
