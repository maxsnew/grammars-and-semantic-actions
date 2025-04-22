open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Properties.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Cubes.Base

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Empty as Empty hiding (⊥;⊥*)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Negation.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open isStrongEquivalence
open StrongEquivalence

-- A grammar is unambiguous if there is at most one term from any
-- other fixed grammar into it
unambiguous : Grammar ℓA → Typeω
unambiguous A = ∀ {ℓB} {B : Grammar ℓB} → (e e' : B ⊢ A) → e ≡ e'

-- A grammar is unambiguous if it is subterminal ---
-- if the unique map to the terminal object (⊤) is a
-- monomorphism
unambiguous' : Grammar ℓA → Typeω
unambiguous' {ℓA = ℓA} A = isMono {A = A}{B = ⊤} (⊤-intro {A = A})

@0 unambiguous'→unambiguous : unambiguous' A → unambiguous A
unambiguous'→unambiguous unambig e e' =
  unambig e e'
    (sym (is-terminal-⊤ .snd (⊤-intro ∘g e)) ∙
         is-terminal-⊤ .snd (⊤-intro ∘g e') )

@0 unambiguous→unambiguous' : unambiguous A → unambiguous' A
unambiguous→unambiguous' unambig e e' ≡! = unambig e e'

-- A grammar is unambiguous if Δ : A ⊢ A & A is a strong equivalence
module _ {A : Grammar ℓA} where
  module _ (π≡ : π₁ ≡ π₂) where
    @0 π≡→unambiguous : unambiguous A
    π≡→unambiguous e e' =
      sym (&-β₁ e e')
      ∙ cong (_∘g e ,& e') π≡
      ∙ &-β₂ e e'

  module _ (Δ≅ : isStrongEquivalence A (A & A) &-Δ) where
    private
      @0 π≡ : π₁ ≡ π₂
      π≡ =
        cong (π₁ ∘g_) (sym (Δ≅ .sec))
        ∙ cong (_∘g Δ≅ .inv) (&-β₁ id id)
        ∙ cong (_∘g Δ≅ .inv) (sym (&-β₂ id id))
        ∙ cong (π₂ ∘g_) (Δ≅ .sec)

    @0 Δ≅→unambiguous : unambiguous A
    Δ≅→unambiguous = π≡→unambiguous π≡

  module _ (unambig : unambiguous A) where
    private
      @0 π≡ : π₁ ≡ π₂
      π≡ = unambig π₁ π₂
    unambiguous→Δ≅ : isStrongEquivalence _ _ &-Δ
    unambiguous→Δ≅ .inv = π₁
    unambiguous→Δ≅ .sec =
      &≡ _ _
        (cong (_∘g π₁) (&-β₁ id id))
        (cong (_∘g π₁) (&-β₂ id id)
        ∙ π≡)
    unambiguous→Δ≅ .ret = &-β₁ id id

disjoint : Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
disjoint A B = A & B ⊢ ⊥

module _ (dis : disjoint A B) (e : C ⊢ A) where
  disjoint⊢ : disjoint C B
  disjoint⊢ = dis ∘g e ,&p id

  module _ (f : D ⊢ B) where
    disjoint⊢2 : disjoint C D
    disjoint⊢2 = disjoint⊢ ∘g id ,&p f

open WeakEquivalence
module _ (dis : disjoint A B) (A≈C : A ≈ C) where
  disjoint≈ : disjoint C B
  disjoint≈ = disjoint⊢ dis (A≈C .inv)

open StrongEquivalence
module _ (dis : disjoint A B) (A≅C : A ≅ C) where
  disjoint≅ : disjoint C B
  disjoint≅ = disjoint⊢ dis (A≅C .inv)

  module _ (B≅D : B ≅ D) where
    @0 disjoint≅2 : disjoint C D
    disjoint≅2 = disjoint≅ ∘g id ,&p B≅D .inv

disjoint⊕l : disjoint (A ⊕ B) C → disjoint A C
disjoint⊕l dis = disjoint⊢ dis inl

disjoint⊕r : disjoint (A ⊕ B) C → disjoint B C
disjoint⊕r dis = disjoint⊢ dis inr

open StrongEquivalence

isUnambiguousRetract' :
  ∀ (f : A ⊢ B) (f' : B ⊢ A)
  → (f' ∘g f ≡ id)
  → unambiguous B → unambiguous A
isUnambiguousRetract' f f' ret unambB e e' =
  cong (_∘g e) (sym ret)
  ∙ cong (f' ∘g_) (unambB _ _)
  ∙ cong (_∘g e') ret

open _isRetractOf_
@0 isUnambiguousRetract : A isRetractOf B → unambiguous B → unambiguous A
isUnambiguousRetract the-ret =
  isUnambiguousRetract' (the-ret .weak .fun) (the-ret .weak .inv) (the-ret .ret)

@0 unambiguous≅ : A ≅ B → unambiguous A → unambiguous B
unambiguous≅ A≅B unambA = isUnambiguousRetract' (A≅B .inv) (A≅B .fun) (A≅B .sec) unambA
  where open isStrongEquivalence

unambiguous→StrongEquivalence
  : unambiguous A
  → unambiguous B
  → (A ⊢ B)
  → (B ⊢ A)
  → A ≅ B
unambiguous→StrongEquivalence unambA unambB f f' =
  mkStrEq f f' (unambB (f ∘g f') id) (unambA (f' ∘g f) id)

unambiguousRetract'→StrongEquivalence
  : ∀ (f : A ⊢ B) (f' : B ⊢ A)
  → (f' ∘g f ≡ id)
  → unambiguous B
  → A ≅ B
unambiguousRetract'→StrongEquivalence f f' ret unambB
  = unambiguous→StrongEquivalence (isUnambiguousRetract' f f' ret unambB) unambB f f'

@0 unambiguousRetract→StrongEquivalence :
  A isRetractOf B → unambiguous B → A ≅ B
unambiguousRetract→StrongEquivalence the-ret unambB =
  unambiguous→StrongEquivalence
    (isUnambiguousRetract the-ret unambB) unambB
    (the-ret .weak .fun) (the-ret .weak .inv)

module _ {A : Grammar ℓA} where
  &⊤≅ : A ≅ A & ⊤
  &⊤≅ .fun = id ,& ⊤-intro
  &⊤≅ .inv = π₁
  &⊤≅ .sec = the-sec
    where
    opaque
      unfolding &-intro ⊤-intro π₁
      the-sec : &⊤≅ .fun ∘g &⊤≅ .inv ≡ id
      the-sec = refl
  &⊤≅ .ret = the-ret
    where
    opaque
      unfolding &-intro ⊤-intro π₁
      the-ret : &⊤≅ .inv ∘g &⊤≅ .fun ≡ id
      the-ret = refl

module _ {A : Grammar ℓA} {B : Grammar ℓB}
  (unambig-A : unambiguous A) (unambig-B : unambiguous B)
  (A≈B : A ≈ B)
  where

  ≈→≅ : A ≅ B
  ≈→≅ .fun = A≈B .fun
  ≈→≅ .inv = A≈B .inv
  ≈→≅ .sec = unambig-B _ _
  ≈→≅ .ret = unambig-A _ _

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (A≅B : A ≅ B)
  where

  ≅→≈ : A ≈ B
  ≅→≈ .fun = A≅B .fun
  ≅→≈ .inv = A≅B .inv
