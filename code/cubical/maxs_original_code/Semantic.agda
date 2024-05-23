module Semantic (C : Set) where

open import Data.Empty
open import Data.Unit
open import Data.List as List
import Data.Maybe as Maybe
open import Data.Product hiding (_<*>_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.All as All
open import Agda.Builtin.Sigma


Σ* : Set
Σ* = List C

Lang : Set₁
Lang = Σ* -> Set


record Sem (Γ : Set) : Set₁ where
  constructor _⊢_
  field
    cod : Γ → Set
    dom : Σ[ i ∈ Γ ] (cod i) → Lang

module _ (Γ : Set) where
  ∣_∣ : ∀ {Γ : Set} → Sem Γ → (Γ → Set)
  ∣ S ∣ = cod S
    where
    open Sem

  _▸_ : (Γ : Set) → (Γ → Set) → Set
  Γ ▸ ∣g∣ = Σ[ i ∈ Γ ] ∣g∣ i

  _⋆_ : (g₁ : Sem Γ) → (g₂ : Sem (Γ ▸ ∣ g₁ ∣)) → Sem Γ
  g₁ ⋆ g₂ =
      (λ i → Σ[ x ∈ X i ] Y (i , x)) ⊢
       λ { (i , x[i] , y[i,x]) w → Σ[ (w₁ , w₂) ∈ (Σ* × Σ*) ] ((w₁ ++ w₂ ≡ w) × P ((i , x[i])) w₁ × Q (((i , x[i])) , y[i,x]) w₂)}
    where
    open Sem
    X = ∣ g₁ ∣
    P = dom g₁
    Y = ∣ g₂ ∣
    Q = dom g₂
  

  


