open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Combinators (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

module _
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  {k : Grammar ℓk}
  {l : Grammar ℓl}
  (g≅h : StrongEquivalence g h)
  (k≅l : StrongEquivalence k l)
  where

  open StrongEquivalence

  concat-strong-equiv : StrongEquivalence (g ⊗ k) (h ⊗ l)
  concat-strong-equiv .fun =
    ⊗-intro (g≅h .fun) (k≅l .fun)
  concat-strong-equiv .inv =
    ⊗-intro (g≅h .inv) (k≅l .inv)
  concat-strong-equiv .sec i = ⊗-intro (g≅h .sec i) (k≅l .sec i)
  concat-strong-equiv .ret i = ⊗-intro (g≅h .ret i) (k≅l .ret i)

  disjunct-strong-equiv : StrongEquivalence (g ⊕ k) (h ⊕ l)
  disjunct-strong-equiv .fun = ⊕-elim (⊕-inl ∘g g≅h .fun) (⊕-inr ∘g k≅l .fun)
  disjunct-strong-equiv .inv = ⊕-elim (⊕-inl ∘g g≅h .inv) (⊕-inr ∘g k≅l .inv)
  disjunct-strong-equiv .sec =
    ⊕≡ _ _
      (λ i → ⊕-inl ∘g g≅h .sec i)
      (λ i → ⊕-inr ∘g k≅l .sec i)
  disjunct-strong-equiv .ret =
    ⊕≡ _ _
      (λ i → ⊕-inl ∘g g≅h .ret i)
      (λ i → ⊕-inr ∘g k≅l .ret i)

module _
  {g : Grammar ℓg}
  (g≅h : StrongEquivalence g h)
  where

  open StrongEquivalence

  the-g*-alg : *r-Algebra g
  the-g*-alg =
    (record { the-ℓ = _
            ; G = KL* h
            ; nil-case = nil
            ; cons-case = cons ∘g ⊗-intro (g≅h .fun) id })

  the-h*-alg : *r-Algebra h
  the-h*-alg =
    (record { the-ℓ = _
            ; G = KL* g
            ; nil-case = nil
            ; cons-case = cons ∘g ⊗-intro (g≅h .inv) id })

  star-strong-equiv : StrongEquivalence (KL* g) (KL* h)
  star-strong-equiv .fun = foldKL*r g the-g*-alg
  star-strong-equiv .inv = foldKL*r h the-h*-alg
  star-strong-equiv .sec =
    !*r-AlgebraHom' h (*r-initial h)
      (record { f = foldKL*r g the-g*-alg ∘g foldKL*r h the-h*-alg 
              ; on-nil = refl
              ; on-cons =
                λ i → cons ∘g ⊗-intro (g≅h .sec i) id ∘g
                  ⊗-intro id (foldKL*r g the-g*-alg ∘g foldKL*r h the-h*-alg) })
      (id*r-AlgebraHom h (*r-initial h))
  star-strong-equiv .ret =
    !*r-AlgebraHom' g (*r-initial g)
      (record { f = foldKL*r h the-h*-alg ∘g foldKL*r g the-g*-alg
              ; on-nil = refl
              ; on-cons =
                λ i → cons ∘g ⊗-intro (g≅h .ret i) id ∘g
                  ⊗-intro id (foldKL*r h the-h*-alg ∘g foldKL*r g the-g*-alg) })
      (id*r-AlgebraHom g (*r-initial g))
