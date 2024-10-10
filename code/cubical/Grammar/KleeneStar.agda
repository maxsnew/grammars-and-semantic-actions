open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term.Base Alphabet

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

module _ (g : Grammar ℓG) where
  data *Tag : Type ℓG where
    nil cons : *Tag

  *Ty : Unit* {ℓG} → Functor Unit*
  *Ty _ = ⊕e *Tag (λ { nil → k ε* ; cons → ⊗e (k g) (Var _)})

  KL* : Grammar ℓG
  KL* = μ *Ty _

  repeatTy : Lift {j = ℓG} ℕ → Functor (Lift ℕ)
  repeatTy (lift zero) = k ε*
  repeatTy (lift (suc n)) = ⊗e (k g) (Var (lift n))

  repeat' : Lift ℕ → Grammar ℓG
  repeat' n = μ repeatTy n

  repeat = ⊕[ n ∈ (Lift ℕ) ] repeat' n

  open StrongEquivalence

  gradeAlg : Algebra *Ty λ _ → repeat
  gradeAlg _ = ⊕ᴰ-elim (λ {
      nil → ⊕ᴰ-in (lift 0) ∘g roll
    ; cons →
        ⊕ᴰ-elim (λ (lift n) → ⊕ᴰ-in (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG) ∘g
        ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
    })

  grade : KL* ⊢ repeat
  grade = rec *Ty gradeAlg _

  ungradeAlg : Algebra repeatTy λ n → KL*
  ungradeAlg (lift zero) = roll ∘g ⊕ᴰ-in nil
  ungradeAlg (lift (suc a)) = roll ∘g ⊕ᴰ-in cons

  ungrade' : ∀ n → repeat' n ⊢ KL*
  ungrade' n = rec repeatTy ungradeAlg n

  ungrade : repeat ⊢ KL*
  ungrade = ⊕ᴰ-elim λ n → ungrade' n

  opaque
    unfolding ⊕ᴰ-distR ⊗-intro eq-π
    secAlg : Algebra repeatTy (λ n → equalizer (grade ∘g ungrade' n) (⊕ᴰ-in n))
    secAlg (lift zero) = eq-intro _ _ roll refl
    secAlg (lift (suc n)) =
      eq-intro _ _
        (roll ∘g id ,⊗ (liftG ∘g eq-π _ _ ∘g lowerG))
        (λ i → ⊕ᴰ-elim (λ (lift m) → ⊕ᴰ-in (lift (suc m)) ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun ∘g
               id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG )

  opaque
    unfolding secAlg ⊕ᴰ-distR eq-π ⊗-intro eq-intro
    *continuous : StrongEquivalence KL* repeat
    *continuous .fun = grade
    *continuous .inv = ungrade
    *continuous .sec =
      ⊕ᴰ≡ _ _ (λ n →
        equalizer-section (grade ∘g ungrade' n) (⊕ᴰ-in n)
          (rec repeatTy secAlg n)
          (ind-id' repeatTy
            (compHomo repeatTy
              (initialAlgebra repeatTy)
              secAlg
              (initialAlgebra repeatTy)
              ((λ m → eq-π _ _) ,
              λ { (lift zero) → refl ; (lift (suc m)) → refl })
              (recHomo repeatTy secAlg))
            n))
    *continuous .ret =
      ind-id' *Ty
        (compHomo *Ty (initialAlgebra *Ty) gradeAlg (initialAlgebra *Ty)
          ((λ _ → ungrade) ,
          (λ _ → ⊕ᴰ≡ _ _
            λ { nil → refl
              ; cons → refl }))
          (recHomo *Ty gradeAlg)) _

NIL : ∀ {g : Grammar ℓG} → ε ⊢ KL* g
NIL = roll ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG

CONS : ∀ {g : Grammar ℓG} → g ⊗ KL* g ⊢ KL* g
CONS = roll ∘g ⊕ᴰ-in cons ∘g liftG ,⊗ liftG

_* : Grammar ℓG → Grammar ℓG
g * = KL* g

-- TODO left handed Kleene star via indexed inductives

--   *l-initial : *l-Algebra
--   *l-initial .the-ℓ = _
--   *l-initial .G = KL*
--   *l-initial .nil-case = nil
--   *l-initial .snoc-case = ans
--     where
--     opaque
--       unfolding _⊗_ ⊗-intro
--       λalg : *r-Algebra
--       λalg .the-ℓ = ℓG
--       λalg .G = KL* ⟜ g
--       λalg .nil-case =
--         ⟜-intro (cons ∘g ⊗-intro id nil ∘g ⊗-unit-r⁻ ∘g ⊗-unit-l)
--       λalg .cons-case =
--         ⟜-intro (cons ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)

--       ans : KL* ⊗ g ⊢ KL*
--       ans = ⟜-intro⁻ (foldKL*r λalg)

--   record *l-AlgebraHom (alg alg' : *l-Algebra) : Typeω where
--     field
--       f : alg .G ⊢ alg' .G
--       on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
--       on-cons : f ∘g alg .snoc-case ≡ alg' .snoc-case ∘g ⊗-intro f id

--   open *l-AlgebraHom

--   module _ (the-l-alg : *l-Algebra) where
--     λalg : *r-Algebra
--     λalg .the-ℓ = the-l-alg .the-ℓ
--     λalg .G = the-l-alg .G ⊸ the-l-alg .G
--     λalg .nil-case = ⊸-intro ⊗-unit-r
--     λalg .cons-case =
--       ⊸-intro {k = the-l-alg .G}
--         (⊸-app ∘g
--         ⊗-intro (the-l-alg .snoc-case) id ∘g
--         ⊗-assoc)

--     KL*l-elim : KL* ⊢ the-l-alg .G
--     KL*l-elim =
--       ⊸-app ∘g
--       ⊗-intro (the-l-alg .nil-case) (foldKL*r λalg) ∘g
--       ⊗-unit-l⁻

--     foldKL*l = KL*l-elim

--     -- TODO prove initiality for the left handed algebra

