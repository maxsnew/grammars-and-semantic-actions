open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Interface (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Epsilon.Interface Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
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

record ⊗Defs {{eps : εStr}} : Typeω where
  field
    _⊗_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
    ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
    ⊗-unit-r : A ⊗ ε ⊢ A
    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
    ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)

    -- the two implementations we have are made from opaque types that need
    -- these helpers to avoid leaking implementation details
    has-split : ∀ (w : String) → (p : (A ⊗ B) w) → (s : Splitting w) → Type ℓ-zero
    @0 isProp-has-split : ∀ (w : String) (p : (A ⊗ B) w) → (s : Splitting w) → isProp (has-split w p s)
    the-split : ∀ (w : String) → (p : (A ⊗ B) w) → Σ[ s ∈ Splitting w ] has-split w p s
    same-splits : {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} {D : Grammar ℓD}
      {w : I → String} → (p : (A ⊗ B) (w i0)) → (q : (C ⊗ D) (w i1)) → Type ℓ-zero
    same-parses : {A : I → Grammar ℓA}{B : I → Grammar ℓB} {w : I → String}
      → (p : (A i0 ⊗ B i0) (w i0)) → (q : (A i1 ⊗ B i1) (w i1)) → (s≡ : same-splits {w = w} p q)
      → Type (ℓ-max ℓA ℓB)

    @0 ⊗PathP : {A : I → Grammar ℓA}{B : I → Grammar ℓB} {w : I → String}
        → {p : (A i0 ⊗ B i0) (w i0)} → {q : (A i1 ⊗ B i1) (w i1)}
        → (s≡ : same-splits {w = w} p q) → same-parses {A = A} {B = B} {w = w} p q s≡
        → PathP (λ i → (A i ⊗ B i) (w i)) p q

    @0 ⊗≡ : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{w}
        → (p p' : (A ⊗ B) w) → (s≡ : same-splits {w = λ _ → w} p p')
        → same-parses {A = λ _ → A} {B = λ _ → B} {w = λ _ → w} p p' s≡
        → p ≡ p'

  _,⊗_ : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
  f ,⊗ g = ⊗-intro f g

open ⊗Defs {{...}} public

record @0 ⊗Equalities {{eps : εStr}} {{⊗defs : ⊗Defs}} : Typeω where
  field
    isSetGrammar⊗ : isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊗ B)

    id,⊗id≡id : id {A = A} ,⊗ id {A = B} ≡ id
    ⊗-intro⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB}
      {C : Grammar ℓC} {D : Grammar ℓD} {E : Grammar ℓE} {F : Grammar ℓF}
      {f : A ⊢ B}{f' : C ⊢ D} {f'' : E ⊢ A} {f''' : F ⊢ C}
     → f ,⊗ f' ∘g f'' ,⊗ f''' ≡ (f ∘g f'') ,⊗ (f' ∘g f''')

    @0 ⊗-unit-rr⁻ : ∀ {A : Grammar ℓA} → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
    @0 ⊗-unit-r⁻r : ∀ {A : Grammar ℓA} → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
    @0 ⊗-unit-ll⁻ : ∀ {A : Grammar ℓA} → ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
    @0 ⊗-unit-l⁻l : ∀ {A : Grammar ℓA} → ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id

    @0 ⊗-unit-rl⁻ : ⊗-unit-r ∘g ⊗-unit-l⁻ ≡ id
    @0 ⊗-unit-lr⁻ : ⊗-unit-l ∘g ⊗-unit-r⁻ ≡ id

    ⊗-unit-r⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} → (f : A ⊢ B) →
      ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
    ⊗-unit-r⁻⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {f : A ⊢ B} →
      ⊗-unit-r⁻ ∘g f ≡ (⊗-intro f id) ∘g ⊗-unit-r⁻
    ⊗-unit-l⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} (f : A ⊢ B) →
      f ∘g ⊗-unit-l ≡ ⊗-unit-l ∘g (⊗-intro id f)
    ⊗-unit-l⁻⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {f : A ⊢ B} →
      ⊗-unit-l⁻ ∘g f ≡ (⊗-intro id f) ∘g ⊗-unit-l⁻

    ⊗-assoc∘⊗-assoc⁻≡id : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} →
      ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
    ⊗-assoc⁻∘⊗-assoc≡id : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} →
      ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id

    ⊗-assoc⁻⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
      {D : Grammar ℓD} {E : Grammar ℓE} {F : Grammar ℓF} →
      {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
      → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'') ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
    ⊗-assoc⊗-intro : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
      {D : Grammar ℓD} {E : Grammar ℓE} {F : Grammar ℓF} →
      {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
      → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'') ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc

    ⊗-assoc⁻⊗-unit-r⁻ : ∀ {A : Grammar ℓA} {B : Grammar ℓB} →
      ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
    ⊗-assoc⊗-unit-l⁻ : ∀ {A : Grammar ℓA} {B : Grammar ℓB} →
      ⊗-assoc {A = A}{C = B} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id

    ⊗-triangle : ∀ {A : Grammar ℓA} {B : Grammar ℓB} →
      ⊗-intro ⊗-unit-r id ∘g ⊗-assoc {A = A}{B = ε}{C = B} ≡ ⊗-intro id ⊗-unit-l
    ⊗-pentagon : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} {D : Grammar ℓD} →
      ⊗-intro (⊗-assoc {A = A}) id ∘g ⊗-assoc ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D}) ≡ ⊗-assoc ∘g ⊗-assoc

  @0 cong-∘g⊗-unit-l⁻ : ∀ {A : Grammar ℓA} {B : Grammar ℓB} →
    (e e' : ε ⊗ A ⊢ B) → (e ∘g ⊗-unit-l⁻ ≡ e' ∘g ⊗-unit-l⁻) → e ≡ e'
  cong-∘g⊗-unit-l⁻ f g ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-ll⁻) ∙
    cong (_∘g ⊗-unit-l) ∘g≡ ∙
    cong (g ∘g_) (⊗-unit-ll⁻)

  @0 cong-∘g⊗-unit-r⁻ : ∀ {A : Grammar ℓA} {B : Grammar ℓB} →
    (e e' : A ⊗ ε ⊢ B) → (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) → e ≡ e'
  cong-∘g⊗-unit-r⁻ {A = A} f f' ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
    cong (_∘g ⊗-unit-r) ∘g≡ ∙
    cong (f' ∘g_) (⊗-unit-rr⁻)
