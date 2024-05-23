module IndexedSemanticActions (C : Set) where

open import Data.Empty
open import Data.Unit
open import Data.List as List
import Data.Maybe as Maybe
open import Data.Product hiding (_<*>_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.All as All
open import Agda.Builtin.Sigma

section : {A B : Set} → (f : A → B) → (g : B → A) → Set
section {B = B} f g = ∀ (b : B) → f (g b) ≡ b

Σ* : Set
Σ* = List C

Lang : Set₁
Lang = Σ* -> Set

⊥L : Lang
⊥L _ = ⊥

⊤L : Lang
⊤L _ = ⊤

Δ : Set → Lang
Δ X = λ _ → X

_×L_ : Lang → Lang → Lang
P ×L Q = λ w → P w × Q w

_⋆L : Lang → Lang
_⋆L P = λ w → Σ[ ws ∈ List Σ* ] (concat ws ≡ w) × All P ws

_⊎L_ : Lang → Lang → Lang
P ⊎L Q = λ w → P w ⊎ Q w

_★L_ : Lang → Lang → Lang
P ★L Q = λ w → Σ[ (u , v) ∈ Σ* × Σ* ] ((u ++ v) ≡ w) × P u × Q v

private
  variable
    P Q L L' : Lang
    X Y Z : Set

record Action (L : Lang) (S : Set) : Set₁ where
  field
    act : Σ[ w ∈ Σ* ] L w → S

⊤p : Action ⊤L ⊤
⊤p = record { act = λ z → tt }

⊥p : Action ⊥L X
⊥p = record { act = λ (_ ,  z) → ⊥-elim z }
  
mapP : (X → Y) → Action L X → Action L Y
mapP f A = record { act = λ x → f (Action.act A x) }

pack : Action L (Σ[ w ∈ Σ* ] L w )
pack = record { act = λ x → x }

pure : X → Action L X
pure x = record { act = λ _ → x }

-- TODO: I think one can also write a version which returns Action (L ★L L') Y
_<*>_ : Action L (X → Y) → Action L' X → Action (L ×L L') Y
record { act = act-f } <*> record { act = act-x } = 
  record { act = λ { (w , L[w] , L'[w]) → (act-f (w , L[w])) (act-x (w , L'[w]))}}

-- TODO: I think one can also write a version which returns Action (L ★L L') Y
_>>=_ : Action L X → (X → Action L' Y) → Action (L ×L L') Y
_>>=_ A k = 
    record { act = λ {(w , l[w] , l'[w]) → Action.act (k (A.act (w , l[w]))) (w , l'[w]) }}
  where
    module A = Action(A)

-- map-All : ∀ {ws} {A : Set} → (∀ {w} → P w → A) → All P ws → List A
-- map-All f [] = []
-- map-All f (px ∷ pxs) = f px ∷ map-All f pxs

-- _* : Action P X → Action (P ⋆L) (List X)
-- record { act = act-x } * =
--   record { act = λ { (w , ws , refl , all-P) → map-All act-x all-P} }

_∨_ : ∀ {L L' : Lang} → Action L X → Action L' X → Action (L ⊎L L') X
_∨_ {X = X} {L = L} {L' = L'} A B = record { act = act }
  where
    module A = Action(A)
    module B = Action(B)

    act : Σ[ w ∈ Σ* ] (L ⊎L L') w → X
    act (w , (inj₁ x)) = A.act (w , x)
    act (w , (inj₂ y)) = B.act (w , y)

_+_ : ∀ {X Y} → Action L X → Action L' Y → Action (L ⊎L L') (X ⊎ Y)
A + B = mapP inj₁ A ∨ mapP inj₂ B


-- idea for cohesive structure
Γ : Action L X → Set
Γ {L = L} {X = X} A = Σ[ f ∈ (X → Σ[ w ∈ Σ* ] L w) ] section A.act f  
  where
    module A = Action(A)

Disc : (X : Set) → Action (Δ X) X
Disc X = record { act = λ (w , x) → x }

CoDisc : (X : Set) → Action (Δ X) ⊤
CoDisc X = record { act = λ _ → tt }
