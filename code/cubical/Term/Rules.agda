open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

module Term.Rules (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

id : g ⊢ g
id _ x = x

seq :
  g ⊢ h →
  h ⊢ k →
  g ⊢ k
seq e e' _ p = e' _ (e _ p)
-- e' (e p)

_∘g_ :
  h ⊢ k →
  g ⊢ h →
  g ⊢ k
_∘g_ e e' = seq e' e

infixr 9 _∘g_
syntax seq e e' = e ⋆ e'

⊗-intro :
  g ⊢ h →
  k ⊢ l →
  g ⊗ k ⊢ h ⊗ l
⊗-intro e e' _ p =
  p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

⊗-unit-r :
  g ⊗ ε-grammar ⊢ g
⊗-unit-r {g = g} _ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) =
  subst g (sym (++-unit-r _)
          ∙ cong (w' ++_) (sym []'≡[])
          ∙ sym w≡w'++[]')
    p⟨w'⟩

⊗-unit-r⁻ :
  g ⊢ g ⊗ ε-grammar
⊗-unit-r⁻ _ p =
  ((_ , []) , (sym (++-unit-r _))) , (p , refl)

isPropε : ∀ w → isProp (ε-grammar w)
isPropε w = isSetString _ _

rectify :
  ∀ {w w'}{g : Grammar ℓg}
  → {p : g w}{q : g w'}
  → {w≡ w≡' : w ≡ w'}
  → PathP (λ i → g (w≡  i)) p q
  → PathP (λ i → g (w≡' i)) p q
rectify {w = w}{w'}{g = g}{p = p}{q = q} = subst {A = w ≡ w'} (λ w≡ → PathP (λ i → g (w≡ i)) p q)
  (isSetString _ _ _ _)

⊗-unit-rr⁻ :
  ∀ {g : Grammar ℓg}
  → ⊗-unit-r⁻ {g = g} ∘g ⊗-unit-r ≡ id
⊗-unit-rr⁻ {g = g} = funExt λ w → funExt λ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) →
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
              hcomp (doubleComp-faces (λ _ → w ++ []) (λ i₂ → ++-unit-r w i₂) i₁)
              (w ++ []))
           i)
          (++-unit-r w (~ i))))
  in
  subst (λ w≡w → subst g w≡w p ≡ p) (isSetString _ _ refl w≡w)
    (substRefl {B = g} p)

⊗-unit-l :
  ε-grammar ⊗ g ⊢ g
⊗-unit-l {g = g} _ p =
  transport
    (cong g (cong (_++  p .fst .fst .snd)
      (sym (p .snd .fst)) ∙ sym (p .fst .snd)))
    (p .snd .snd)

⊗-unit-l⁻ :
  g ⊢ ε-grammar ⊗ g
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
  subst (λ w≡w → subst g w≡w p ≡ p) (isSetString _ _ refl w≡w) (substRefl {B = g} p)

cong-∘g⊗-unit-l⁻ :
  (e e' : ε-grammar ⊗ g ⊢ h) →
  (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) →
  e ≡ e'
cong-∘g⊗-unit-l⁻ f g ∘g≡ =
  cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
  cong (_∘g ⊗-unit-l) ∘g≡ ∙
  cong (g ∘g_) (⊗-unit-ll⁻)

cong-∘g⊗-unit-r⁻ :
  (e e' : g ⊗ ε-grammar ⊢ h) →
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
  isSetString w [] ((⊗-unit-r ∘g ⊗-unit-l⁻) w p) (id {g = ε-grammar} w p)

⊗-assoc :
  g ⊗ (h ⊗ k) ⊢ (g ⊗ h) ⊗ k
⊗-assoc _ p =
  ((fst p .fst .fst ++ fst (p .snd .snd) .fst .fst , fst (p .snd .snd) .fst .snd) ,
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
  (((fst (p .snd .fst) .fst .fst) , (fst (p .snd .fst) .fst .snd ++ fst p .fst .snd)) ,
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

-⊗-intro :
  g ⊗ h ⊢ k →
  h ⊢ g -⊗ k
-⊗-intro e _ p w' q =
  e _ ((_ , refl) , (q , p))

-⊗-app :
  g ⊗ (g -⊗ h) ⊢ h
-⊗-app {h = h} _ p = subst h (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

-⊗-intro⁻ :
  g ⊢ h -⊗ k →
  h ⊗ g ⊢ k
-⊗-intro⁻ {h = h}{k = k} f =
  -⊗-app ∘g (⊗-intro (id {g = h}) f)

-⊗-intro∘-⊗-intro⁻≡id :
  (e : g ⊢ h -⊗ k) →
  -⊗-intro {g = h}{h = g}{k = k}(-⊗-intro⁻ e) ≡ e
-⊗-intro∘-⊗-intro⁻≡id e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ ph → transportRefl _

-⊗-intro⁻∘-⊗-intro≡id :
  (e : g ⊗ h ⊢ k) →
  -⊗-intro⁻ {g = h}{h = g}{k = k}(-⊗-intro e) ≡ e
-⊗-intro⁻∘-⊗-intro≡id {k = k} e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP (≡-× refl refl) (≡-× refl refl)))


-- TODO : this needs a better name
-⊗-curry :
  (g -⊗ h) ⊗ k ⊢ g -⊗ (h ⊗ k)
-⊗-curry {g = g}{h = h}{k = k} =
  -⊗-intro {g = g}{h = (g -⊗ h) ⊗ k}{k = h ⊗ k}
    (⊗-assoc ⋆ ⊗-intro -⊗-app id)

-⊗-β :
  (m : (g ⊗ h) ⊢ k) →
  (-⊗-intro⁻ {g = h}{h = g}{k = k} (-⊗-intro {g = g}{h = h}{k = k} m))
    ≡
  m
-⊗-β {k = k} m = funExt (λ w → funExt (λ p⊗ →
  fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
    (congP (λ _ → m _) (⊗PathP refl refl))))

-⊗-η :
  (f : g ⊢ h -⊗ k) →
  f
    ≡
  (-⊗-intro {g = h}{h = g}{k = k} (-⊗-intro⁻ {g = g}{h = h}{k = k} f))
-⊗-η f = funExt (λ w → funExt (λ p⊗ → funExt (λ w' → funExt
  (λ q⊗ → sym (transportRefl (f _ p⊗ w' q⊗))))))


⟜-intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⊗- h
⟜-intro e _ p w' q =
  e _ ((_ , refl) , p , q)

⟜-app :
  (g ⊗- h) ⊗ h ⊢ g
⟜-app {g = g} _ (((w' , w'') , w≡w'++w'') , f , inp) =
  subst g (sym w≡w'++w'') (f _ inp)

⟜-intro⁻ :
  g ⊢ h ⊗- k →
  g ⊗ k ⊢ h
⟜-intro⁻ {h = h}{k = k} f =
  ⟜-app ∘g ⊗-intro f (id {g = k})

⟜-η :
  (e : g ⊢ h ⊗- k) →
  ⟜-intro {g = g}{h = k}{k = h}(⟜-intro⁻ e) ≡ e
⟜-η e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ pk → transportRefl _

⟜-β :
  (e : g ⊗ h ⊢ k) →
  ⟜-intro⁻ {g = g}{h = k}{k = h}(⟜-intro e) ≡ e
⟜-β e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP refl refl))

⟜-curry :
  g ⊗ (h ⊗- k) ⊢ (g ⊗ h) ⊗- k
⟜-curry {g = g}{h = h}{k = k} =
  ⟜-intro (⊗-intro id ⟜-app ∘g ⊗-assoc⁻)

⟜UMP : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
  → Iso (g ⊗ h ⊢ k) (g ⊢ k ⊗- h)
⟜UMP {k = k} = iso ⟜-intro ⟜-intro⁻ (⟜-η {h = k}) ⟜-β

⊤-intro :
  g ⊢ ⊤-grammar {ℓG = ℓ}
⊤-intro _ _ = tt*

⊥-elim :
  ⊥-grammar ⊢ g
⊥-elim _ = ⊥.elim

⊥-η : ∀ (f f' : ⊥-grammar ⊢ g)
  → f ≡ f'
⊥-η _ _ = funExt λ _ → funExt ⊥.elim

&-intro :
  g ⊢ h →
  g ⊢ k →
  g ⊢ h & k
&-intro e e' _ p =
  e _ p , e' _ p

&-π₁ :
  g & h ⊢ g
&-π₁ _ p = p .fst

&-π₂ :
  g & h ⊢ h
&-π₂ _ p = p .snd

&-β₁ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₁ 
    ≡
  e₁
&-β₁ e₁ e₂ = refl

&-β₂ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₂
    ≡
  e₂
&-β₂ e₁ e₂ = refl

&-η :
  (e : g ⊢ h & k) →
  (&-intro {g = g}{h = h}{k = k}
    (e ⋆ &-π₁)
    (e ⋆ &-π₂))
  ≡
  e
&-η e = refl

⊕-inl :
  g ⊢ g ⊕ h
⊕-inl _ p = inl p

⊕-inr :
  g ⊢ h ⊕ g
⊕-inr _ p = inr p

⊕-elim :
  g ⊢ h →
  k ⊢ h →
  g ⊕ k ⊢ h
⊕-elim eg eh _ p =
  Sum.elim
    (λ pg → eg _ pg)
    (λ ph → eh _ ph)
    p

⊕≡ :
  (f f' : g ⊕ k ⊢ h)
  → (f ∘g ⊕-inl ≡ f' ∘g ⊕-inl)
  → (f ∘g ⊕-inr ≡ f' ∘g ⊕-inr)
  → f ≡ f'
⊕≡ f f' f≡f'inl f≡f'inr = funExt λ w → funExt λ
  { (inl x) → funExt⁻ (funExt⁻ f≡f'inl _) x
  ; (inr x) → funExt⁻ (funExt⁻ f≡f'inr _) x }

⊕-βl :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inl ⋆ ⊕-elim e₁ e₂
    ≡
  e₁
⊕-βl e₁ e₂ = refl

⊕-βr :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inr ⋆ ⊕-elim e₁ e₂
    ≡
  e₂
⊕-βr e₁ e₂ = refl

⊕-η :
  (e : g ⊕ h ⊢ k) →
  (⊕-elim {g = g}{h = k}{k = h}
    (⊕-inl ⋆ e)
    (⊕-inr ⋆ e)
  )
    ≡
    e
⊕-η e i _ (inl x) = e _ (inl x)
⊕-η e i _ (inr x) = e _ (inr x)

⊗-dist-over-⊕ :
  g ⊗ (h ⊕ k) ⊢ (g ⊗ h) ⊕ (g ⊗ k)
⊗-dist-over-⊕ {g = g}{h = h}{k = k} =
  -⊗-intro⁻ {g = h ⊕ k}{h = g}{k = (g ⊗ h) ⊕ (g ⊗ k)}
    (⊕-elim {g = h}{h = g -⊗ ((g ⊗ h) ⊕ (g ⊗ k))}{k = k}
      (-⊗-intro {g = g}{h = h}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inl)
      (-⊗-intro {g = g}{h = k}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inr))

⇒-intro :
  g & h ⊢ k →
  g ⊢ h ⇒ k
⇒-intro e _ pg = λ ph → e _ (pg , ph)

⇒-app :
  (g ⇒ h) & g ⊢ h
⇒-app _ (f , pg) = f pg

⇒-intro⁻ :
  g ⊢ h ⇒ k
  → g & h ⊢ k
⇒-intro⁻ f = ⇒-app ∘g &-intro (f ∘g &-π₁) &-π₂
