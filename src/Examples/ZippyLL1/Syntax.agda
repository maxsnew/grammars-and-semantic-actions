{- A port of the development from
   Edelman, Hamza and Kuncak, Zippy LL(1) parsing with derivatives, PLDI 2020
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.FinSet

module Examples.ZippyLL1.Syntax
  (Alphabet : hSet ℓ-zero)
  (Kind : FinSet ℓ-zero) -- Should probably be a FinOrd for simplicity
  (getKind : ⟨ Alphabet ⟩ → ⟨ Kind ⟩)
  where

open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar Alphabet
open import Term Alphabet
open import SemanticAction.Base Alphabet


Ctx = TypeWithStr ℓ-zero λ Γ → Γ → Type ℓ-zero

data Syntax (Γ : Ctx) -- variables
            : (V : Type ℓ-zero) → Type (ℓ-suc ℓ-zero) -- values
            where
  elem : ∀ (k : ⟨ Kind ⟩) → Syntax Γ ⟨ Alphabet ⟩
  var  : ∀ (x : ⟨ Γ ⟩) → Syntax Γ (str Γ x)
  [⊥]    : ∀ {V} → Syntax Γ V
  _[∨]_  : ∀ {V} → Syntax Γ V → Syntax Γ V → Syntax Γ V
  [ε]    : Syntax Γ Unit
  _[·]_  : ∀ {V1 V2} → Syntax Γ V1 → Syntax Γ V2 → Syntax Γ (V1 × V2)
  _⊚_  : ∀ {V1 V2} → (V1 → V2) → Syntax Γ V1 → Syntax Γ V2

-- A syntax defines simultaneously a grammar and a semantic action over that grammar
⟦_⟧0 : ∀ {Γ V} → Syntax Γ V → Functor ⟨ Γ ⟩
⟦ elem [k] ⟧0 =
  ⊕e (Σ[ tok ∈ ⟨ Alphabet ⟩ ] getKind tok Eq.≡ [k]) λ (tok , _) →
  k (literal tok)
⟦ var x ⟧0 = Var x
⟦ [⊥] ⟧0 = ⊕e Empty.⊥ λ ()
⟦ s [∨] s' ⟧0 = ⊕e Bool λ { true → ⟦ s ⟧0 ; false → ⟦ s' ⟧0 }
⟦ [ε] ⟧0 = k ε
⟦ s [·] s' ⟧0 = ⟦ s ⟧0 ⊗e ⟦ s' ⟧0
⟦ f ⊚ s ⟧0 = ⟦ s ⟧0

⟦_⟧1 : ∀ {Γ V} → (S : Syntax Γ V) → ⟦ ⟦ S ⟧0 ⟧ (λ x → Pure (str Γ x)) ⊢ Pure V
⟦ elem k₁ ⟧1 = Pure-intro fst
⟦ var x ⟧1 = lowerG
⟦ [⊥] ⟧1 = Pure-intro (λ ())
⟦ S [∨] S' ⟧1 = ⊕ᴰ-elim (λ where
  false → ⟦ S' ⟧1
  true → ⟦ S ⟧1)
⟦ [ε] ⟧1 = σ _ ∘g ⊤-intro
⟦ S [·] S' ⟧1 =
  (⊕ᴰ-elim λ x → ⊕ᴰ-elim λ x' → σ (x , x') ∘g ⊤-intro)
  ∘g map⊕ᴰ (λ _ → ⊕ᴰ-distR .StrongEquivalence.fun)
  ∘g ⊕ᴰ-distL .StrongEquivalence.fun ∘g ⟦ S ⟧1 ,⊗ ⟦ S' ⟧1
⟦ f ⊚ S ⟧1 = Pure-intro f ∘g ⟦ S ⟧1

Syntaxes : Ctx → Type _
Syntaxes Γ = ∀ (x : ⟨ Γ ⟩) → Syntax Γ (str Γ x)

Syntax→SemanticAction
  : ∀ {Γ} → (S : Syntaxes Γ)
  → SemanticAction (λ x → ⟦ S x ⟧0) (str Γ)
Syntax→SemanticAction S x = ⟦ S x ⟧1
