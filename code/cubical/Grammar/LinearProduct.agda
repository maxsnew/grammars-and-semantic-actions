open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_⊗'_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊗' g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)
infixr 5 _⊗'_
opaque
  _⊗_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  _⊗_ = _⊗'_
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

  -- because ⊗ is opaque,
  -- same-splits and same-parses are needed so that the interface of
  -- ⊗ doesn't leak in the type signature of ⊗PathP
  same-splits :
    {g : I → Grammar ℓg}{h : I → Grammar ℓh}
    {w : I → String}
    → (p : (g i0 ⊗ h i0) (w i0))
    → (q : (g i1 ⊗ h i1) (w i1))
    → Type ℓ-zero
  same-splits p q = p .fst .fst ≡ q .fst .fst

  same-parses :
    {g : I → Grammar ℓg}{h : I → Grammar ℓh}
    {w : I → String}
    → (p : (g i0 ⊗ h i0) (w i0))
    → (q : (g i1 ⊗ h i1) (w i1))
    → (s≡ : same-splits {g = g}{h = h}{w = w} p q)
    → Type (ℓ-max ℓg ℓh)
  same-parses {g = g} {h = h} p q s≡ =
    PathP (λ i → g i (s≡ i .fst) × h i (s≡ i .snd)) (p .snd) (q .snd)

  ⊗PathP :
    {g : I → Grammar ℓg}{h : I → Grammar ℓh}
    {w : I → String}
    → {p : (g i0 ⊗ h i0) (w i0)}
    → {q : (g i1 ⊗ h i1) (w i1)}
    → (s≡ : same-splits {g = g} {h = h} {w = w} p q)
    → same-parses p q s≡
    → PathP (λ i → (g i ⊗ h i) (w i)) p q
  ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

  ⊗≡ : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{w}
    → (p p' : (g ⊗ h) w)
    → (s≡ : same-splits {g = λ _ → g}{h = λ _ → h}{w = λ _ → w} p p')
    → same-parses p p' s≡
    → p ≡ p'
  ⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡

  ⊗-intro :
    g ⊢ h →
    k ⊢ l →
    g ⊗ k ⊢ h ⊗ l
  ⊗-intro e e' _ p =
    p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

  opaque
    unfolding ε
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

    isPropε : ∀ w → isProp (ε w)
    isPropε w = isSetString _ _

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
          , isProp→PathP (λ _ → isPropε _) refl []'≡[]))

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

    -- TODO this proof seems overly complicated
    ⊗-unit-r⊗-intro :
      (f : g ⊢ h) →
      ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
    ⊗-unit-r⊗-intro f =
      cong-∘g⊗-unit-r⁻ (⊗-unit-r ∘g ⊗-intro f id) (f ∘g ⊗-unit-r)
        ((⊗-unit-r ∘g ⊗-intro f id) ∘g ⊗-unit-r⁻
          ≡⟨ refl ⟩
          ⊗-unit-r ∘g ⊗-unit-r⁻ ∘g f
          ≡⟨ ((λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))) ⟩
        (f ∘g ⊗-unit-r) ∘g ⊗-unit-r⁻
        ∎)
        -- (cong (_∘g f) {!sym ⊗-unit-rr⁻!})
      -- ⊗-unit-r ∘g ⊗-intro f id
      --   ≡⟨ {!cong-∘g⊗-unit-r!} ⟩
      -- f ∘g ⊗-unit-r
      -- ∎

    ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
    ⊗-unit-rl⁻ = funExt λ w → funExt λ p →
      isSetString w [] ((⊗-unit-r ∘g ⊗-unit-l⁻) w p) (id {g = ε} w p)

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

  opaque
    unfolding ε ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro :
      ∀ {f : g ⊢ h}
      → ⊗-unit-l⁻ ∘g f
      ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻
    ⊗-unit-l⁻⊗-intro = refl

    ⊗-unit-r⁻⊗-intro :
      ∀ {f : g ⊢ h}
      → ⊗-unit-r⁻ ∘g f
      ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
    ⊗-unit-r⁻⊗-intro = refl

    id,⊗id≡id : ⊗-intro id id ≡ id {g = g ⊗ h}
    id,⊗id≡id = refl

_,⊗_ = ⊗-intro
infixr 20 _,⊗_
