open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g''' g'''' g''''' : Grammar ℓg
    h h' h'' h''' h'''' h''''' : Grammar ℓh
    f f' f'' f''' f'''' f''''' : g ⊢ h
    k : Grammar ℓk
    l : Grammar ℓl

_⊗'_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊗' g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)
infixr 5 _⊗'_
opaque
  _⊗_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  _⊗_ = _⊗'_

  isSetGrammar⊗ : isSetGrammar g → isSetGrammar h → isSetGrammar (g ⊗ h)
  isSetGrammar⊗ isSetG isSetH w = isSetΣ (isSetSplitting w)
    λ _ → isSet× (isSetG _) (isSetH _)

infixr 5 _⊗_

opaque
  unfolding _⊗_
  ⊗-elim : g ,, h ⊢ k → g ⊗ h ⊢ k
  ⊗-elim {k = k} f w (((w1 , w2) , w≡w1++w2) , gp , hp) =
    subst k (sym w≡w1++w2) (f w1 w2 gp hp)

  ⊗-intro' : g ,, h ⊢ (g ⊗ h)
  ⊗-intro' w1 w2 gp hp = splitting++ w1 w2 , gp , hp

  ⊗-β : ∀ (f : g ,, h ⊢ k)
    → (⊗-elim {k = k} f ∘b ⊗-intro') ≡ f
  ⊗-β {k = k} f i w1 w2 gp hp = substRefl {B = k} (f w1 w2 gp hp) i

  -- ⊗-η : ∀ (f : g ⊗ h ⊢ k)
  --   → f ≡ ⊗-elim {k = k} (f ∘b ⊗-intro')
  -- ⊗-η f i w x = {!!}

opaque
  unfolding _⊗_
  -- because ⊗ is opaque,
  -- same-splits and same-parses are needed so that the interface of
  -- ⊗ doesn't leak in the type signature of ⊗PathP
  has-split :
    ∀ (w : String) → (p : (g ⊗ h) w) → (s : Splitting w) → Type ℓ-zero
  has-split w p s = s ≡ p .fst

  isProp-has-split : ∀ (w : String) (p : (g ⊗ h) w) → (s : Splitting w) → isProp (has-split w p s)
  isProp-has-split w p s = isSetSplitting w _ _

  the-split :
    ∀ (w : String) → (p : (g ⊗ h) w) → Σ[ s ∈ Splitting w ] has-split w p s
  the-split w p = (p .fst) , refl

same-splits :
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  {k : Grammar ℓk}
  {l : Grammar ℓl}
  {w : I → String}
  → (p : (g ⊗ h) (w i0))
  → (q : (k ⊗ l) (w i1))
  → Type ℓ-zero
same-splits {w = w} p q =
    (the-split (w i0) p .fst .fst) ≡ (the-split (w i1) q .fst .fst)

opaque
  unfolding _⊗_ the-split

  same-parses :
    {g : I → Grammar ℓg}{h : I → Grammar ℓh}
    {w : I → String}
    → (p : (g i0 ⊗ h i0) (w i0))
    → (q : (g i1 ⊗ h i1) (w i1))
    → (s≡ : same-splits {w = w} p q)
    → Type (ℓ-max ℓg ℓh)
  same-parses {g = g} {h = h} p q s≡ =
    PathP (λ i → g i (s≡ i .fst) × h i (s≡ i .snd)) (p .snd) (q .snd)

  ⊗PathP :
    {g : I → Grammar ℓg}{h : I → Grammar ℓh}
    {w : I → String}
    → {p : (g i0 ⊗ h i0) (w i0)}
    → {q : (g i1 ⊗ h i1) (w i1)}
    → (s≡ : same-splits {w = w} p q)
    → same-parses {g = g} {h = h} {w = w} p q s≡
    → PathP (λ i → (g i ⊗ h i) (w i)) p q
  ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

  ⊗≡ : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{w}
    → (p p' : (g ⊗ h) w)
    → (s≡ : same-splits {w = λ _ → w} p p')
    → same-parses {g = λ _ → g} {h = λ _ → h} {w = λ _ → w} p p' s≡
    → p ≡ p'
  ⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡

  opaque
    unfolding _⊗_
    ⊗≡' : ∀ {g : Grammar ℓg}{h : Grammar ℓh}
      → (e f : g ⊗ h ⊢ k ⊗ l)
      → (se≡ :
        ∀ (w : String)
        → (p : (g ⊗ h) w)
        → same-splits {w = λ _ → w} p (e w p))
      → (sf≡ :
        ∀ (w : String)
        → (p : (g ⊗ h) w)
        → same-splits {w = λ _ → w} p (f w p))
      → (p≡ : ∀ (w : String)
         → (p : (g ⊗ h) w)
         → same-parses {g = λ _ → k} {h = λ _ → l} {w = λ _ → w} (e w p) (f w p)
           (sym (se≡ w p) ∙ sf≡ w p))
      → e ≡ f
    ⊗≡' e f se≡ sf≡ p≡ = funExt λ w → funExt λ p →
      ΣPathP (
        ΣPathP ((sym (se≡ w p) ∙ sf≡ w p) ,
          isProp→PathP (λ i → isSetString _ _) _ _) ,
        (p≡ w p))

opaque
  unfolding _⊗_ the-split
  ⊗-intro :
    g ⊢ h →
    k ⊢ l →
    g ⊗ k ⊢ h ⊗ l
  ⊗-intro e e' _ p =
    p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

opaque
  unfolding _⊗_ the-split
  ⊗-in : {w w' : String} →
    g w → h w' → (g ⊗ h) (w ++ w')
  ⊗-in p q = (_ , refl) , (p , q)

opaque
  unfolding _⊗_ the-split ⊗-intro ⊗≡
  ⊗-intro⊗-intro
    : ∀ {f : g ⊢ g'}{f' : g'' ⊢ g'''}
        {f'' : g'''' ⊢ g}
        {f''' : g''''' ⊢ g''}
    → ⊗-intro f f' ∘g ⊗-intro f'' f'''
      ≡ ⊗-intro (f ∘g f'') (f' ∘g f''')
  ⊗-intro⊗-intro = refl

  opaque
    unfolding ε ⊗≡
    ⊗-unit-r :
      g ⊗ ε ⊢ g
    ⊗-unit-r {g = g} _ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) =
      subst g (sym (++-unit-r _)
              ∙ cong (w' ++_) (sym []'≡[])
              ∙ sym w≡w'++[]')
            p⟨w'⟩

    ⊗-unit-r⁻ :
      g ⊢ g ⊗ ε
    ⊗-unit-r⁻ _ p =
      ((_ , []) , (sym (++-unit-r _))) , (p , refl)

    rectify :
      ∀ {w w'}{g : Grammar ℓg}
      → {p : g w}{q : g w'}
      → {w≡ w≡' : w ≡ w'}
      → PathP (λ i → g (w≡  i)) p q
      → PathP (λ i → g (w≡' i)) p q
    rectify {w = w}{w'}{g = g}{p = p}{q = q} =
      subst {A = w ≡ w'} (λ w≡ → PathP (λ i → g (w≡ i)) p q)
        (isSetString _ _ _ _)

    ⊗-unit-rr⁻ :
      ∀ {g : Grammar ℓg}
      → ⊗-unit-r⁻ {g = g} ∘g ⊗-unit-r ≡ id
    ⊗-unit-rr⁻ {g = g} =
      funExt λ w → funExt λ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) →
      let w≡w' = (sym (sym (++-unit-r _)
              ∙ cong (w' ++_) (sym []'≡[])
              ∙ sym w≡w'++[]'))
      in
      ⊗≡ _ _
        (≡-× w≡w'
          (sym []'≡[]))
        (ΣPathP
          ( symP (subst-filler g (sym w≡w') p⟨w'⟩)
          , isProp→PathP (λ _ → isLangε _) refl []'≡[]))

    ⊗-unit-r⁻r : ∀ {g : Grammar ℓg}
      → ⊗-unit-r {g = g} ∘g ⊗-unit-r⁻ ≡ id
    ⊗-unit-r⁻r {g = g} = funExt λ w → funExt λ p →
      let
        w≡w : w ≡ w
        w≡w =       (λ i →
             (hcomp
              (doubleComp-faces (λ _ → w)
               (λ i₁ →
                  hcomp (doubleComp-faces (λ _ → w ++ [])
                    (λ i₂ → ++-unit-r w i₂) i₁)
                  (w ++ []))
               i)
              (++-unit-r w (~ i))))
      in
      subst (λ w≡w → subst g w≡w p ≡ p) (isSetString _ _ refl w≡w)
        (substRefl {B = g} p)

    ⊗-unit-l :
      ε ⊗ g ⊢ g
    ⊗-unit-l {g = g} _ p =
      transport
        (cong g (cong (_++  p .fst .fst .snd)
          (sym (p .snd .fst)) ∙ sym (p .fst .snd)))
        (p .snd .snd)

    ⊗-unit-l⁻ :
      g ⊢ ε ⊗ g
    ⊗-unit-l⁻ _ p =
      (([] , _) , refl) , (refl , p)

    ⊗-unit-ll⁻ :
      ⊗-unit-l⁻ {g = g} ∘g ⊗-unit-l ≡ id
    ⊗-unit-ll⁻ {g = g} = funExt λ w → funExt λ p⊗ →
      let
        w'≡w : p⊗ .fst .fst .snd ≡ w
        w'≡w =
          (λ i →
              (hcomp
               (doubleComp-faces (λ _ → p⊗ .fst .fst .snd)
                (λ i₁ → p⊗ .fst .snd (~ i₁)) i)
               (p⊗ .snd .fst (~ i) ++ p⊗ .fst .fst .snd)))
        in
       ⊗≡ _ _
         (≡-× (sym (p⊗ .snd .fst)) (sym w'≡w))
         (ΣPathP ((isProp→PathP (λ i → isSetString _ _) _ _) ,
         symP (subst-filler g w'≡w (p⊗ .snd .snd))))

    ⊗-unit-l⁻l :
      ⊗-unit-l {g = g} ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-l⁻l {g = g} = funExt λ w → funExt λ p →
      let w≡w = λ i →
                   ((λ i₁ →
                       ⊗-unit-l⁻ {g = g} w p .snd .fst (~ i₁) ++
                         ⊗-unit-l⁻ {g = g} w p .fst .fst .snd)
                    ∙ (λ i₁ → ⊗-unit-l⁻ {g = g} w p .fst .snd (~ i₁)))
                   i
      in
      subst (λ w≡w → subst g w≡w p ≡ p)
        (isSetString _ _ refl w≡w) (substRefl {B = g} p)

    cong-∘g⊗-unit-l⁻ :
      (e e' : ε ⊗ g ⊢ h) →
      (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
      e ≡ e'
    cong-∘g⊗-unit-l⁻ f g ∘g≡ =
      cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
      cong (_∘g ⊗-unit-l) ∘g≡ ∙
      cong (g ∘g_) (⊗-unit-ll⁻)

    cong-∘g⊗-unit-r⁻ :
      (e e' : g ⊗ ε ⊢ h) →
      (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
      e ≡ e'
    cong-∘g⊗-unit-r⁻ f g ∘g≡ =
      cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
      cong (_∘g ⊗-unit-r) ∘g≡ ∙
      cong (g ∘g_) (⊗-unit-rr⁻)


    ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-rl⁻ = funExt λ w → funExt λ p →
      isSetString w [] ((⊗-unit-r ∘g ⊗-unit-l⁻) w p) (id {g = ε} w p)

    --technically this follows from more basic monoidal category axioms but it's not simple
    ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id
    ⊗-unit-lr⁻ = funExt λ w → funExt λ p →
      isSetString w [] ((⊗-unit-l ∘g ⊗-unit-r⁻ ) w p) ((id {g = ε} w p))

  ⊗-unit-r' :
    g ⊗ ε ⊢ g
  ⊗-unit-r' = ⊗-elim (ε-elim-r id)

  ⊗-unit-r'⁻ : g ⊢ g ⊗ ε
  ⊗-unit-r'⁻ = ⊗-intro' b∘εr ε-intro

  ⊗-assoc :
    g ⊗ (h ⊗ k) ⊢ (g ⊗ h) ⊗ k
  ⊗-assoc _ p =
    ((fst p .fst .fst ++ fst (p .snd .snd) .fst .fst ,
      fst (p .snd .snd) .fst .snd) ,
      p .fst .snd ∙
      cong (p .fst .fst .fst ++_) (p .snd .snd .fst .snd) ∙
      sym
      (++-assoc
        (p .fst .fst .fst)
        (p .snd .snd .fst .fst .fst)
        (p .snd .snd .fst .fst .snd))) ,
    ((((fst p .fst .fst , fst (p .snd .snd) .fst .fst) ,
      refl) ,
    ((p .snd .fst) , (p .snd .snd .snd .fst))) , (p .snd .snd .snd .snd))

  ⊗-assoc⁻ :
    (g ⊗ h) ⊗ k ⊢ g ⊗ (h ⊗ k)
  ⊗-assoc⁻ _ p =
    (((fst (p .snd .fst) .fst .fst) ,
      (fst (p .snd .fst) .fst .snd ++ fst p .fst .snd)) ,
      (p .fst .snd ∙
      cong (_++ p .fst .fst .snd) (p .snd .fst .fst .snd) ∙
      ++-assoc
        (p .snd .fst .fst .fst .fst)
        (p .snd .fst .fst .fst .snd)
        (p .fst .fst .snd))) ,
      (p .snd .fst .snd .fst ,
      ((_ , refl) ,
      (p .snd .fst .snd .snd ,
      p .snd .snd)))

  ⊗-assoc∘⊗-assoc⁻≡id :
   ⊗-assoc {g = g}{h = h}{k = k} ∘g ⊗-assoc⁻ ≡ id
  ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ p →
    ⊗≡ _ _
      (≡-× (λ i → p .snd .fst .fst .snd (~ i)) refl)
      (ΣPathP (
        (⊗PathP
          (≡-× refl refl)
          (≡-× refl refl)) ,
        refl))

  ⊗-assoc⁻∘⊗-assoc≡id :
   ⊗-assoc⁻ {g = g}{h = h}{k = k} ∘g ⊗-assoc ≡ id
  ⊗-assoc⁻∘⊗-assoc≡id = funExt λ w → funExt λ p →
    ⊗≡ _ _
      (≡-× refl (sym (p .snd .snd .fst .snd)))
      (ΣPathP (
        refl ,
        (⊗PathP (≡-× refl refl)
          (ΣPathP (refl , refl)))))

  ⊗-assoc⁻⊗-intro :
    ∀ {f : g ⊢ h}{f' : g' ⊢ h'}{f'' : g'' ⊢ h''}
    → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
    ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
  ⊗-assoc⁻⊗-intro = refl

  ⊗-assoc⊗-intro :
    ∀ {f : g ⊢ h}{f' : g' ⊢ h'}{f'' : g'' ⊢ h''}
    → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
      ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
  ⊗-assoc⊗-intro = funExt λ w → funExt λ p →
    ⊗≡ _ _ (≡-× refl refl) (ΣPathP (refl , refl))

  opaque
    unfolding ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ :
      ⊗-assoc⁻ {g = g}{h = h} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
    ⊗-assoc⁻⊗-unit-r⁻ = funExt λ w → funExt λ p →
      ⊗≡ _ _ (≡-× refl (++-unit-r _))
        (ΣPathP (refl , ⊗PathP refl refl))

  opaque
    unfolding ⊗-unit-l⁻
    ⊗-assoc⊗-unit-l⁻ :
     ⊗-assoc {g = g}{k = k} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
    ⊗-assoc⊗-unit-l⁻ = funExt λ w → funExt λ p →
      ⊗≡ _ _ (≡-× (++-unit-r _) refl) (ΣPathP (⊗PathP refl refl , refl))

  opaque
    unfolding ε ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro :
      ∀ {f : g ⊢ h}
      → ⊗-unit-l⁻ ∘g f
      ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro = refl

    ⊗-unit-l⊗-intro :
      ∀ (f : g ⊢ h)
      → f ∘g ⊗-unit-l
        ≡ ⊗-unit-l ∘g (⊗-intro id f)
    ⊗-unit-l⊗-intro f =
      cong-∘g⊗-unit-l⁻ _ _
        λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

    ⊗-unit-r⁻⊗-intro :
      ∀ {f : g ⊢ h}
      → ⊗-unit-r⁻ ∘g f
      ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
    ⊗-unit-r⁻⊗-intro = refl

    -- this is the fact that the inverse of a natural transformation is natural
    ⊗-unit-r⊗-intro :
      (f : g ⊢ h) →
      ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
    ⊗-unit-r⊗-intro f =
      cong-∘g⊗-unit-r⁻ _ _
        (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

    id,⊗id≡id : ⊗-intro id id ≡ id {g = g ⊗ h}
    id,⊗id≡id = refl

_,⊗_ = ⊗-intro
infixr 20 _,⊗_

{- ε* versions of the unitors  -}
⊗-unit*-l : ε* {ℓ} ⊗ g ⊢ g
⊗-unit*-l = ⊗-unit-l ∘g ⊗-intro lowerG id

⊗-unit*-l⁻ : g ⊢ ε* {ℓ} ⊗ g
⊗-unit*-l⁻ = ⊗-intro liftG id ∘g ⊗-unit-l⁻

opaque
  unfolding ⊗-intro
  ⊗-unit*-l⊗-intro :
      ∀ (f : g ⊢ h)
      → f ∘g ⊗-unit*-l {ℓ}
        ≡ ⊗-unit*-l ∘g (⊗-intro id f)
  ⊗-unit*-l⊗-intro f =
    cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl
  ⊗-unit*-ll⁻ :
    ⊗-unit*-l⁻ {g = g} {ℓ = ℓ} ∘g ⊗-unit*-l ≡ id
  ⊗-unit*-ll⁻ i = ⊗-intro liftG id ∘g ⊗-unit-ll⁻ i ∘g ⊗-intro lowerG id

  ⊗-unit*-l⁻l :
    ⊗-unit*-l {ℓ = ℓ} {g = g} ∘g ⊗-unit*-l⁻ ≡ id
  ⊗-unit*-l⁻l = ⊗-unit-l⁻l

⊗-unit*-r : g ⊗ ε* {ℓ} ⊢ g
⊗-unit*-r = ⊗-unit-r ∘g ⊗-intro id lowerG

⊗-unit*-r⁻ : g ⊢ g ⊗ ε* {ℓ}
⊗-unit*-r⁻ = ⊗-intro id liftG ∘g ⊗-unit-r⁻

opaque
  unfolding ⊗-intro
  ⊗-unit*-r⊗-intro :
      ∀ (f : g ⊢ h)
      → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
        ≡ f ∘g ⊗-unit*-r
  ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

  ⊗-unit*-rr⁻ :
    ⊗-unit*-r⁻ {g = g} {ℓ = ℓ} ∘g ⊗-unit*-r ≡ id
  ⊗-unit*-rr⁻ i = ⊗-intro id liftG ∘g ⊗-unit-rr⁻ i ∘g ⊗-intro id lowerG

  ⊗-unit*-r⁻r :
    ⊗-unit*-r {g = g} {ℓ = ℓ} ∘g ⊗-unit*-r⁻ ≡ id
  ⊗-unit*-r⁻r = ⊗-unit-r⁻r

{- Triangle -}
opaque
  unfolding ⊗-intro ⊗-unit-r ⊗-unit-l ⊗-assoc
  ⊗-triangle :
    ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {g = g}{h = ε* {ℓ}}{k = h}
    ≡ ⊗-intro id ⊗-unit*-l
  ⊗-triangle {g = g}{h = h} = funExt λ w → funExt λ {
    (((w1 , w2) , w≡w1w2) ,
     (gp , (((w3 , w4) , w2≡w3w4) , ((lift w3≡[]) , hp)))) →
    let p1 : w1 ++ w3 ≡ w1
        p1 = (cong (w1 ++_) w3≡[] ∙ ++-unit-r _)
        p2 = (cong (_++ w4) (sym w3≡[]) ∙ sym w2≡w3w4)
        p1' : w1 ≡ w1 ++ w3
        p1' = λ i → (hcomp
           (doubleComp-faces (λ _ → w1)
            (λ i₁ →
               hcomp (doubleComp-faces (λ _ → w1 ++ []) (λ i₂ → w1 ++ w3) i₁)
               (w1 ++ w3≡[] (~ i₁)))
            i)
           (++-unit-r w1 (~ i)))
    in
    ⊗≡ _ _ (≡-× p1 p2)
     (ΣPathP (rectify {g = g} {w≡ = sym p1'}{w≡' = p1}
       (symP (transport-filler (cong g p1') gp))
     , transport-filler (cong h p2) hp))
    }

{- Pentagon -}
opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-pentagon :
    ⊗-intro (⊗-assoc {g = g}) id
    ∘g ⊗-assoc
    ∘g ⊗-intro id (⊗-assoc {g = g'}{h = g''}{k = g'''})
      ≡
    ⊗-assoc
    ∘g ⊗-assoc
  ⊗-pentagon {g = g1}{g' = g2}{g'' = g3}{g''' = g4} =
    funExt λ w → funExt λ {
    (((w1 , w234) , w≡w1w234) , p1 ,
    (((w2 , w34) , w234≡w2w34) , p2 ,
    (((w3 , w4) , w34≡w3w4) , (p3 , p4)))) →
    ⊗≡ _ _
    (≡-× (sym (++-assoc w1 w2 w3)) refl)
    (ΣPathP ((⊗PathP (≡-× refl refl) refl) , refl))
    }

{- Big associators and big diagrams -}

⊗-assoc⁻3 :
  (g ⊗ g' ⊗ g'') ⊗ g''' ⊢ g ⊗ g' ⊗ g'' ⊗ g'''
⊗-assoc⁻3 = id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻

⊗-assoc3 :
  g ⊗ g' ⊗ g'' ⊗ g''' ⊢ (g ⊗ g' ⊗ g'') ⊗ g'''
⊗-assoc3 = ⊗-assoc ∘g id ,⊗ ⊗-assoc

⊗-assoc⁻3⊗-unit-r⁻ :
  ⊗-assoc⁻3 {g = g}{g' = g'}{g'' = g''} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻3⊗-unit-r⁻ =
  cong (id ,⊗ ⊗-assoc⁻ ∘g_) ⊗-assoc⁻⊗-unit-r⁻
  ∙ ⊗-intro⊗-intro
  ∙ cong (id ,⊗_) ⊗-assoc⁻⊗-unit-r⁻

⊗-assoc⁻4 :
  (g ⊗ g' ⊗ g'' ⊗ g''') ⊗ g'''' ⊢ g ⊗ g' ⊗ g'' ⊗ g''' ⊗ g''''
⊗-assoc⁻4 = id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻

⊗-assoc4 :
  g ⊗ g' ⊗ g'' ⊗ g''' ⊗ g'''' ⊢ (g ⊗ g' ⊗ g'' ⊗ g''') ⊗ g''''
⊗-assoc4 = ⊗-assoc ∘g id ,⊗ ⊗-assoc3

⊗-assoc⁻4⊗-unit-r⁻ :
  ⊗-assoc⁻4 {g = g}{g' = g'}{g'' = g''}{g''' = g'''} ∘g ⊗-unit-r⁻
  ≡ id ,⊗ id ,⊗ id ,⊗ ⊗-unit-r⁻
⊗-assoc⁻4⊗-unit-r⁻ =
  cong (id ,⊗ ⊗-assoc⁻3 ∘g_) ⊗-assoc⁻⊗-unit-r⁻
  ∙ ⊗-intro⊗-intro
  ∙ cong (id ,⊗_) ⊗-assoc⁻3⊗-unit-r⁻

-- ⊗-assoc⁻3⊗-intro :
--   ∀ {f f' f'' f'''} →
--   (⊗-assoc⁻3 {g = g}{g' = g'}{g'' = g''}{g''' = g'''} ∘g (f ,⊗ f' ,⊗ f'') ,⊗ f''')
--   ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ∘g (⊗-assoc⁻3 {g = h}{g' = h'}{g'' = h''}{g''' = h'''}))
-- ⊗-assoc⁻3⊗-intro =
--   {!!}
opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-assoc⁻4⊗-intro :
    ∀ {f f' f'' f''' f''''} →
    (⊗-assoc⁻4 {g = g}{g' = g'}{g'' = g''}{g''' = g'''}{g'''' = g''''} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
    ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {g = h}{g' = h'}{g'' = h''}{g''' = h'''}{g'''' = h''''}))
  ⊗-assoc⁻4⊗-intro = refl

opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-assoc3⊗-assoc⁻3 : ⊗-assoc3 {g = g}{g' = g'}{g'' = g''}{g''' = g'''} ∘g ⊗-assoc⁻3 ≡ id
  ⊗-assoc3⊗-assoc⁻3 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc∘⊗-assoc⁻≡id i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
    ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩ id ∎

  ⊗-assoc4⊗-assoc⁻4 : ⊗-assoc4 {g = g}{g' = g'}{g'' = g''}{g''' = g'''}{g'''' = g''''} ∘g ⊗-assoc⁻4 ≡ id
  ⊗-assoc4⊗-assoc⁻4 =
    ⊗-assoc ∘g id ,⊗ ⊗-assoc3 ∘g id ,⊗ ⊗-assoc⁻3 ∘g ⊗-assoc⁻
      ≡⟨ (λ i → ⊗-assoc ∘g id ,⊗ ⊗-assoc3⊗-assoc⁻3 i ∘g ⊗-assoc⁻) ⟩
    ⊗-assoc ∘g ⊗-assoc⁻
      ≡⟨ ⊗-assoc∘⊗-assoc⁻≡id ⟩
    id ∎

  ⊗-assoc⁻3⊗-assoc3 : ⊗-assoc⁻3 {g = g}{g' = g'}{g'' = g''}{g''' = g'''} ∘g ⊗-assoc3 ≡ id
  ⊗-assoc⁻3⊗-assoc3 =
    id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻ ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
      ≡⟨ (λ i → id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻∘⊗-assoc≡id i ∘g id ,⊗ ⊗-assoc) ⟩
    id ,⊗ (⊗-assoc⁻ ∘g ⊗-assoc) ≡⟨ ((λ i → id ,⊗ ⊗-assoc⁻∘⊗-assoc≡id i)) ⟩
    id ∎

  ⊗-assoc⁻4⊗-assoc4 : ⊗-assoc⁻4 {g = g}{g' = g'}{g'' = g''}{g''' = g'''}{g'''' = g''''} ∘g ⊗-assoc4 ≡ id
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

