{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Indexed.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (_⊕_ ;_or_)
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
  ; balanced' → ⊗e (k (literal [)) (⊗e (Var _) (⊗e (k (literal ])) (Var _))) })
IndDyck : Grammar ℓ-zero
IndDyck = μ DyckTy _

data TraceTag : Type where
  eof' open' close' leftovers' unexpected' : TraceTag
TraceTys : ℕ × Bool → Functor (ℕ × Bool)
TraceTys (n , b) = ⊕e TraceTag (λ
  { eof' → ⊕e (n Eq.≡ zero) (λ _ → ⊕e (b Eq.≡ true) λ _ → k ε)
  ; open' → ⊗e (k (literal [)) (Var (suc n , b))
  ; close' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊗e (k (literal ])) (Var (n-1 , b))
  ; leftovers' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊕e (b Eq.≡ false) λ _ → k ε
  ; unexpected' → ⊕e ((n , b) Eq.≡ (0 , false)) λ _ → ⊗e (k (literal ])) (k ⊤)
  })

Trace : ℕ → Bool → Grammar ℓ-zero
Trace n b = μ TraceTys (n , b)

opaque
  unfolding _⊗_ ⊗-intro
  parse : string ⊢ &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace n b
  parse = foldKL*r _ (record { the-ℓ = ℓ-zero ; G = _
    ; nil-case = LinΠ-intro (Nat.elim
      (LinΣ-intro true ∘g roll ∘g LinΣ-intro eof' ∘g LinΣ-intro Eq.refl ∘g LinΣ-intro Eq.refl ∘g id)
      (λ n-1 _ → LinΣ-intro false ∘g roll ∘g LinΣ-intro leftovers' ∘g LinΣ-intro (_ , Eq.refl) ∘g LinΣ-intro Eq.refl ∘g id))
    ; cons-case = LinΠ-intro λ n → ⟜-intro⁻ (LinΣ-elim (λ
      { [ → ⟜-intro {k = Goal n} (⊸-intro⁻ (
        (LinΣ-elim λ b → ⊸-intro {k = Goal n}
          (LinΣ-intro b ∘g roll ∘g LinΣ-intro open'))
        ∘g LinΠ-app (suc n)))
      ; ] → ⟜-intro {k = Goal n} (Nat.elim {A = λ n → _ ⊢ Goal n}
          (LinΣ-intro false ∘g roll ∘g LinΣ-intro unexpected' ∘g LinΣ-intro Eq.refl ∘g id ,⊗ ⊤-intro)
          (λ n-1 _ →
          ⊸-intro⁻ ((LinΣ-elim λ b → ⊸-intro {k = Goal (suc n-1)} (LinΣ-intro b ∘g roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , Eq.refl)))
            ∘g LinΠ-app n-1))
          n) })) })
    where
      Goal : ℕ → Grammar ℓ-zero
      Goal n = ⊕[ b ∈ Bool ] Trace n b

  mkTree : Trace zero true ⊢ IndDyck
  mkTree = ⊗-unit-r ∘g rec TraceTys alg (0 , true) where
    Stk : ℕ → Grammar ℓ-zero
    Stk = Nat.elim ε λ _ Stk⟨n⟩ → literal ] ⊗ IndDyck ⊗ Stk⟨n⟩
    GenIndDyck : ℕ × Bool → Grammar ℓ-zero
    GenIndDyck (n , false) = ⊤
    GenIndDyck (n , true) = IndDyck ⊗ Stk n
    alg : Algebra TraceTys GenIndDyck
    alg (n , b) = LinΣ-elim (λ
      { eof' → LinΣ-elim (λ { Eq.refl → LinΣ-elim λ { Eq.refl → (roll ∘g LinΣ-intro nil') ,⊗ id ∘g ⊗-unit-r⁻ } })
      ; open' → Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc n , b)  ⊢ GenIndDyck (n , b)}
          (⟜4⊗ (⟜4-intro-ε (roll ∘g LinΣ-intro balanced')))
          ⊤-intro b
      ; close' → LinΣ-elim (λ { (n-1 , Eq.refl) → Bool.elim
                                                   {A =
                                                    λ b →
                                                      Term (literal ] ⊗ GenIndDyck (n-1 , b)) (GenIndDyck (suc n-1 , b))}
        (⟜0⊗ (roll ∘g LinΣ-intro nil'))
        ⊤-intro
        b } )
      ; leftovers' → LinΣ-elim λ { (n-1 , Eq.refl) → LinΣ-elim λ { Eq.refl → ⊤-intro } }
      ; unexpected' → LinΣ-elim λ { Eq.refl → ⊤-intro }
      })

  exhibitTrace' : IndDyck ⊢ Trace zero true
  exhibitTrace' = ((⟜-app ∘g ⊸0⊗ (roll ∘g LinΣ-intro eof' ∘g LinΣ-intro Eq.refl ∘g LinΣ-intro Eq.refl)) ∘g LinΠ-app 0) ∘g rec DyckTy alg _ where
    Goal : Unit → Grammar ℓ-zero
    Goal _ = &[ n ∈ ℕ ] (Trace n true ⟜ Trace n true)
    alg : Algebra DyckTy Goal
    alg _ = LinΣ-elim (λ
      { nil' → LinΠ-intro (λ n → ⟜-intro-ε id)
      ; balanced' → LinΠ-intro λ n → ⟜-intro {k = Trace n true}
        (roll ∘g LinΣ-intro open'
        ∘g id ,⊗ ((⟜-app ∘g LinΠ-app (suc n) ,⊗ ((roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , Eq.refl) ∘g id ,⊗ (⟜-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
        ∘g ⊗-assoc⁻)
      })
