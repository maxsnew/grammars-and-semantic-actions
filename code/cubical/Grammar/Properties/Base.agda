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
open import Grammar.HLevels Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Negation Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ ℓ' ℓg ℓh ℓk ℓl ℓS : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open isStrongEquivalence
open StrongEquivalence

-- A grammar is unambiguous if there is at most one term from any
-- other fixed grammar into it
unambiguous : Grammar ℓg → Typeω
unambiguous g = ∀ {ℓh} {h : Grammar ℓh} → (e e' : h ⊢ g) → e ≡ e'

-- A grammar is unambiguous if it is subterminal ---
-- if the unique map to the terminal object (⊤) is a
-- monomorphism
unambiguous' : Grammar ℓg → Typeω
unambiguous' {ℓg = ℓg} g = isMono {g = g}{h = ⊤} (⊤-intro {g = g})

unambiguous'→unambiguous : unambiguous' g → unambiguous g
unambiguous'→unambiguous unambig e e' =
  unambig e e'
    (sym (is-terminal-⊤ .snd (⊤-intro ∘g e)) ∙
         is-terminal-⊤ .snd (⊤-intro ∘g e') )

unambiguous→unambiguous' : unambiguous g → unambiguous' g
unambiguous→unambiguous' unambig e e' ≡! = unambig e e'

-- A grammar is unambiguous if Δ : g ⊢ g & g is a strong equivalence
module _ {g : Grammar ℓg} where
  private
    π₁ = &-π₁ {g = g} {h = g}
    π₂ = &-π₂ {g = g} {h = g}
    Δ = &-Δ {g = g}

  module _ (π≡ : π₁ ≡ π₂) where
    π≡→unambiguous : unambiguous g
    π≡→unambiguous e e' =
      sym (&-β₁ e e')
      ∙ cong (_∘g e ,& e') π≡
      ∙ &-β₂ e e'

  module _ (Δ≅ : isStrongEquivalence _ _ Δ) where
    private
      π≡ : π₁ ≡ π₂
      π≡ =
        cong (π₁ ∘g_) (sym (Δ≅ .sec))
        ∙ cong (_∘g Δ≅ .inv) (&-β₁ id id)
        ∙ cong (_∘g Δ≅ .inv) (sym (&-β₂ id id))
        ∙ cong (π₂ ∘g_) (Δ≅ .sec)

    Δ≅→unambiguous : unambiguous g
    Δ≅→unambiguous = π≡→unambiguous π≡

  module _ (unambig : unambiguous g) where
    private
      π≡ : π₁ ≡ π₂
      π≡ = unambig π₁ π₂
    unambiguous→Δ≅ : isStrongEquivalence _ _ Δ
    unambiguous→Δ≅ .inv = π₁
    unambiguous→Δ≅ .sec =
      &≡ _ _
        (cong (_∘g π₁) (&-β₁ id id))
        (cong (_∘g π₁) (&-β₂ id id)
        ∙ π≡)
    unambiguous→Δ≅ .ret = &-β₁ id id

-- rename to "unambiguously parseable?"
totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

disjoint : Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
disjoint g h = g & h ⊢ ⊥


module _ (dis : disjoint g h) (e : k ⊢ g) where
  disjoint⊢ : disjoint k h
  disjoint⊢ = dis ∘g e ,&p id

  module _ (f : l ⊢ h) where
    disjoint⊢2 : disjoint k l
    disjoint⊢2 = disjoint⊢ ∘g id ,&p f

open LogicalEquivalence
module _ (dis : disjoint g h) (g≈k : LogicalEquivalence g k) where
  disjoint≈ : disjoint k h
  disjoint≈ = disjoint⊢ dis (g≈k .inv)

open StrongEquivalence
module _ (dis : disjoint g h) (g≅k : g ≅ k) where
  disjoint≅ : disjoint k h
  disjoint≅ = disjoint⊢ dis (g≅k .inv)

  module _ (h≅l : h ≅ l) where
    disjoint≅2 : disjoint k l
    disjoint≅2 = disjoint≅ ∘g id ,&p h≅l .inv

disjoint⊕l : disjoint (g ⊕ h) k → disjoint g k
disjoint⊕l dis = disjoint⊢ dis ⊕-inl

disjoint⊕r : disjoint (g ⊕ h) k → disjoint h k
disjoint⊕r dis = disjoint⊢ dis ⊕-inr

open StrongEquivalence

opaque
  unfolding ⊤-intro
  totallyParseable→unambiguous' :
    totallyParseable g → unambiguous' g
  totallyParseable→unambiguous' parseable =
    Mono∘g ⊕-inl _
      (isStrongEquivalence→isMono
        (parseable .snd .fun)
        (StrongEquivalence→isStrongEquivalence _ _ (parseable .snd)))
      isMono-⊕-inl
totallyParseable→unambiguous :
  totallyParseable g → unambiguous g
totallyParseable→unambiguous parseable =
  unambiguous'→unambiguous (totallyParseable→unambiguous' parseable)

parser : Grammar ℓg → Type (ℓ-suc ℓg)
parser {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] (disjoint g g' × (⊤ ⊢ g ⊕ g'))

decidable : Grammar ℓg → Type ℓg
decidable g = ⊤ ⊢ g ⊕ ¬G g

isUnambiguousRetract :
  ∀ (f : g ⊢ h) (f' : h ⊢ g)
  → (f' ∘g f ≡ id)
  → unambiguous h → unambiguous g
isUnambiguousRetract f f' ret unambH e e' =
  cong (_∘g e) (sym ret)
  ∙ cong (f' ∘g_) (unambH _ _)
  ∙ cong (_∘g e') ret

unambiguous≅ : StrongEquivalence g h → unambiguous g → unambiguous h
unambiguous≅ g≅h unambG = isUnambiguousRetract (g≅h .inv) (g≅h .fun) (g≅h .sec) unambG
  where open isStrongEquivalence

unambiguous→StrongEquivalence
  : unambiguous g
  → unambiguous h
  → (g ⊢ h)
  → (h ⊢ g)
  → StrongEquivalence g h
unambiguous→StrongEquivalence unambG unambH f f' =
  mkStrEq f f' (unambH (f ∘g f') id) (unambG (f' ∘g f) id)

unambiguousRetract→StrongEquivalence
  : ∀ (f : g ⊢ h) (f' : h ⊢ g)
  → (f' ∘g f ≡ id)
  → unambiguous h
  → StrongEquivalence g h
unambiguousRetract→StrongEquivalence f f' ret unambH
  = unambiguous→StrongEquivalence (isUnambiguousRetract f f' ret unambH) unambH f f'

module _ {g : Grammar ℓg} where
  &⊤≅ : g ≅ g & ⊤
  &⊤≅ .fun = id ,& ⊤-intro
  &⊤≅ .inv = &-π₁
  &⊤≅ .sec = the-sec
    where
    opaque
      unfolding &-intro ⊤-intro
      the-sec : &⊤≅ .fun ∘g &⊤≅ .inv ≡ id
      the-sec = refl
  &⊤≅ .ret = the-ret
    where
    opaque
      unfolding &-intro ⊤-intro
      the-ret : &⊤≅ .inv ∘g &⊤≅ .fun ≡ id
      the-ret = refl

module _
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  (unambig-g : unambiguous g)
  (unambig-h : unambiguous h)
  (g≈h : g ≈ h)
  where

  ≈→≅ : g ≅ h
  ≈→≅ .fun = g≈h .fun
  ≈→≅ .inv = g≈h .inv
  ≈→≅ .sec = unambig-h _ _
  ≈→≅ .ret = unambig-g _ _

module _
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  (g≅h : g ≅ h)
  where

  ≅→≈ : g ≈ h
  ≅→≈ .fun = g≅h .fun
  ≅→≈ .inv = g≅h .inv
