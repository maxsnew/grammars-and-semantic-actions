module Examples.Indexed.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_ ;_or_)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat as Nat
open import Cubical.Data.List hiding (init; rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

open import Examples.Dyck
open import Grammar Alphabet
open import Grammar.Maybe Alphabet hiding (μ)
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet

data DyckTag : Type ℓ-zero where
  nil' balanced' : DyckTag
DyckTy : Unit → Functor Unit
DyckTy _ = ⊕e DyckTag (λ
  { nil' → k ε
  ; balanced' → ⊗e (k (literal [)) (⊗e (Var _) (⊗e (k (literal [)) (Var _))) })
IndDyck : Grammar ℓ-zero
IndDyck = μ DyckTy _

data TraceTag : Type where
  eof' open' close' leftovers' unexpected' : TraceTag
TraceTys : ℕ × Bool → Functor (ℕ × Bool)
TraceTys (n , b) = ⊕e TraceTag (λ
  { eof' → ⊕e (n ≡ zero) (λ _ → ⊕e (b ≡ true) λ _ → k ε)
  ; open' → ⊗e (k (literal [)) (Var (suc n , b))
  ; close' → ⊕e (fiber suc n) λ (n-1 , _) → ⊗e (k (literal ])) (Var (n-1 , b))
  ; leftovers' → ⊕e (fiber suc n) λ (n-1 , _) → ⊕e (b ≡ false) λ _ → k ε
  ; unexpected' → ⊕e ((n , b) ≡ (0 , false)) λ _ → ⊗e (k (literal ])) (k ⊤)
  })

Trace : ℕ → Bool → Grammar _
Trace n b = μ TraceTys (n , b)

parse : string ⊢ &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace n b
parse = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = LinΠ-intro (Nat.elim
    (LinΣ-intro true ∘g roll ∘g LinΣ-intro eof' ∘g LinΣ-intro refl ∘g LinΣ-intro refl ∘g id)
    (λ n-1 _ → LinΣ-intro false ∘g roll ∘g LinΣ-intro leftovers' ∘g LinΣ-intro (_ , refl) ∘g LinΣ-intro refl ∘g id))
  ; cons-case = LinΠ-intro λ n → ⟜-intro⁻ (LinΣ-elim (λ
    { [ → ⟜-intro {k = Goal n} (⊸-intro⁻ (
      (LinΣ-elim λ b → ⊸-intro {k = Goal n}
        (LinΣ-intro b ∘g roll ∘g LinΣ-intro open'))
      ∘g LinΠ-app (suc n)))
    ; ] → ⟜-intro {k = Goal n} (Nat.elim {A = λ n → _ ⊢ Goal n}
        (LinΣ-intro false ∘g roll ∘g LinΣ-intro unexpected' ∘g LinΣ-intro refl ∘g id ,⊗ ⊤-intro)
        (λ n-1 _ →
        ⊸-intro⁻ ((LinΣ-elim λ b → ⊸-intro {k = Goal (suc n-1)} (LinΣ-intro b ∘g roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , refl)))
          ∘g LinΠ-app n-1))
        n) })) })
  where
    Goal : ℕ → Grammar _
    Goal n = ⊕[ b ∈ _ ] Trace n b
