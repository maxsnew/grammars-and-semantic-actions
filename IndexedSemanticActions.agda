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


Σ* : Set
Σ* = List C

Lang : Set₁
Lang = Σ* -> Set

⊥L : Lang
⊥L _ = ⊥

⊤L : Lang
⊤L _ = ⊤

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
    act : ∀ {w} → L w → S

⊤p : Action ⊤L ⊤
⊤p = record { act = λ z → tt }

⊥p : Action ⊥L X
⊥p = record { act = λ z → ⊥-elim z }
  
mapP : (X → Y) → Action L X → Action L Y
mapP f A = record { act = λ x → f (Action.act A x) }

pack : Action L (Σ[ w ∈ Σ* ] L w )
pack = record { act = λ {w} x → (w , x) }

pure : X → Action L X
pure x = record { act = λ _ → x }

-- TODO: I think one can also write a version which returns Action (L ★L L') Y
_<*>_ : Action L (X → Y) → Action L' X → Action (L ×L L') Y
record { act = act-f } <*> record { act = act-x } = 
  record { act = λ { (L[w] , L'[w]) → (act-f L[w]) (act-x L'[w])}}

-- TODO: I think one can also write a version which returns Action (L ★L L') Y
_>>=_ : Action L X → (X → Action L' Y) → Action (L ×L L') Y
_>>=_ A k = 
    record { act = λ {(l[w] , l'[w]) → Action.act (k (A.act l[w])) l'[w] }}
  where
    module A = Action(A)

map-All : ∀ {ws} {A : Set} → (∀ {w} → P w → A) → All P ws → List A
map-All f [] = []
map-All f (px ∷ pxs) = f px ∷ map-All f pxs

_* : Action P X → Action (P ⋆L) (List X)
record { act = act-x } * =
  record { act = λ { (ws , refl , all-P) → map-All act-x all-P} }

_∨_ : ∀ {L L' : Lang} → Action L X → Action L' X → Action (L ⊎L L') X
_∨_ {X = X} {L = L} {L' = L'} A B = record { act = act }
  where
    module A = Action(A)
    module B = Action(B)

    act : ∀ {w} → (L ⊎L L') w → X
    act (inj₁ x) = A.act x
    act (inj₂ y) = B.act y

_+_ : ∀ {X Y} → Action L X → Action L' Y → Action (L ⊎L L') (X ⊎ Y)
A + B = mapP inj₁ A ∨ mapP inj₂ B
