open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.KleeneStar ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

module _ (g : Grammar ℓG) where
  data KL* : Grammar ℓG
    where
    nil : ε-grammar ⊢ KL*
    cons : g ⊗ KL* ⊢ KL*

  record *r-Algebra : Typeω where
    field
      the-ℓ : Level
      G : Grammar the-ℓ
      nil-case : ε-grammar ⊢ G
      cons-case : g ⊗ G ⊢ G

  open *r-Algebra

  *r-initial : *r-Algebra
  *r-initial .the-ℓ = _
  *r-initial .G = KL*
  *r-initial .nil-case = nil
  *r-initial .cons-case = cons


  record *r-AlgebraHom (alg alg' : *r-Algebra) : Typeω where
    field
      f : alg .G ⊢ alg' .G
      on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
      on-cons : f ∘g alg .cons-case ≡ alg' .cons-case ∘g ⊗-intro id f

  open *r-AlgebraHom

  module _ (the-alg : *r-Algebra) where
    id*r-AlgebraHom : *r-AlgebraHom the-alg the-alg
    id*r-AlgebraHom .f = id
    id*r-AlgebraHom .on-nil = refl
    id*r-AlgebraHom .on-cons = refl

    KL*r-elim : KL* ⊢ the-alg .G
    KL*r-elim _ (nil _ x) = the-alg .nil-case _ x
    KL*r-elim _ (cons _ x) =
      the-alg .cons-case _
        ((x .fst) , ((x .snd .fst) , (KL*r-elim _ (x .snd .snd))))

    foldKL*r = KL*r-elim

    ∃*r-AlgebraHom : *r-AlgebraHom *r-initial the-alg
    ∃*r-AlgebraHom .f = KL*r-elim
    ∃*r-AlgebraHom .on-nil = refl
    ∃*r-AlgebraHom .on-cons = refl

    !*r-AlgebraHom :
      (e : *r-AlgebraHom *r-initial the-alg) →
      ∀ w p →
      e .f w p ≡ KL*r-elim w p
    !*r-AlgebraHom e _ (nil _ x) = funExt⁻ (funExt⁻ (e .on-nil) _) x
    !*r-AlgebraHom e _ (cons _ x) =
      funExt⁻ (funExt⁻ (e .on-cons) _) x ∙
      (λ i → the-alg .cons-case _
        (x .fst , x .snd .fst , !*r-AlgebraHom e _ (x .snd .snd) i))

    !*r-AlgebraHom' :
      (e e' : *r-AlgebraHom *r-initial the-alg) →
      e .f ≡ e' .f
    !*r-AlgebraHom' e e' = funExt λ w → funExt λ p →
      !*r-AlgebraHom e w p ∙ sym (!*r-AlgebraHom e' w p)

  record *l-Algebra : Typeω where
    field
      the-ℓ : Level
      G : Grammar the-ℓ
      nil-case : ε-grammar ⊢ G
      snoc-case : G ⊗ g ⊢ G

  open *l-Algebra


  -- λalg-initial : *r-Algebra
  -- λalg-initial .the-ℓ = ℓG
  -- λalg-initial .G = KL* -⊗ KL*
  -- λalg-initial .nil-case = -⊗-intro ⊗-unit-r
  -- λalg-initial .cons-case =
  --   -⊗-intro (-⊗-app ∘g ⊗-intro {!!} id ∘g ⊗-assoc)

  *l-initial : *l-Algebra
  *l-initial .the-ℓ = _
  *l-initial .G = KL*
  *l-initial .nil-case = nil
  *l-initial .snoc-case =
    ⟜-intro⁻ (foldKL*r λalg)
    where
    λalg : *r-Algebra
    λalg .the-ℓ = ℓG
    λalg .G = KL* ⊗- g
    λalg .nil-case =
      ⟜-intro (cons ∘g ⊗-intro id nil ∘g ⊗-unit-r⁻ ∘g ⊗-unit-l)
    λalg .cons-case =
      ⟜-intro (cons ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)

  record *l-AlgebraHom (alg alg' : *l-Algebra) : Typeω where
    field
      f : alg .G ⊢ alg' .G
      on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
      on-cons : f ∘g alg .snoc-case ≡ alg' .snoc-case ∘g ⊗-intro f id

  open *l-AlgebraHom

  module _ (the-l-alg : *l-Algebra) where
    λalg : *r-Algebra
    λalg .the-ℓ = the-l-alg .the-ℓ
    λalg .G = the-l-alg .G -⊗ the-l-alg .G
    λalg .nil-case = -⊗-intro ⊗-unit-r
    λalg .cons-case =
      -⊗-intro {k = the-l-alg .G}
        (-⊗-app ∘g
        ⊗-intro (the-l-alg .snoc-case) id ∘g
        ⊗-assoc)

    KL*l-elim : KL* ⊢ the-l-alg .G
    KL*l-elim =
      -⊗-app ∘g
      ⊗-intro (the-l-alg .nil-case) (foldKL*r λalg) ∘g
      ⊗-unit-l⁻

    foldKL*l = KL*l-elim

    -- TODO prove initiality for the left handed algebra
    -- ∃*l-AlgebraHom : *l-AlgebraHom *l-initial the-l-alg
    -- ∃*l-AlgebraHom .f =
    --   -⊗-app ∘g
    --   ⊗-intro (the-l-alg .nil-case) (foldKL*r λalg) ∘g
    --   ⊗-unit-l⁻
    -- ∃*l-AlgebraHom .on-nil =
    --   -⊗-app ∘g
    --     ⊗-intro id (-⊗-intro ⊗-unit-r) ∘g ⊗-intro (the-l-alg .nil-case) id ∘g ⊗-unit-l⁻
    --     ≡⟨ (λ i → -⊗-β ⊗-unit-r i ∘g ⊗-intro (the-l-alg .nil-case) id ∘g ⊗-unit-l⁻) ⟩
    --   ⊗-unit-r ∘g ⊗-intro (the-l-alg .nil-case) id ∘g ⊗-unit-l⁻
    --     ≡⟨ (λ i → ⊗-unit-r⊗-intro (the-l-alg .nil-case) i ∘g ⊗-unit-l⁻) ⟩
    --   the-l-alg .nil-case ∘g ⊗-unit-r ∘g ⊗-unit-l⁻
    --     ≡⟨ cong (the-l-alg .nil-case ∘g_) ⊗-unit-rl⁻ ⟩
    --   the-l-alg .nil-case
    --   ∎
    -- ∃*l-AlgebraHom .on-cons =
    --   (-⊗-app ∘g
    --     ⊗-intro (the-l-alg .nil-case) (foldKL*r λalg) ∘g ⊗-unit-l⁻)
    --    ∘g ⟜-intro⁻ {!!}
    --     ≡⟨ {!!} ⟩
    --   {!!}
    --   ∎
