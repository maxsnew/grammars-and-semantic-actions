module SemanticActions (Char : Set) where

open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality


Lang : Set₁
Lang = List Char -> Set

record Action (S : Set) : Set₁ where
  field
    L : Lang
    act : ∀ {w} → L w → S

record CorrectParse {S} (A : Action S) (w : List Char) (s : S) : Set where
  field
    tree : Action.L A w
    correct : Action.act A tree ≡ s

record Parser {S} (A : Action S) : Set where
  field
    parse : List Char → Maybe S
    parseJust : ∀ w s → parse w ≡ just s → CorrectParse A w s
    parseNothing : ∀ w → parse w ≡ nothing → Action.L A w → ⊥

⊤p : Action ⊤
⊤p = record { L = λ _ → ⊤ ; act = λ z → tt }

⊥p : ∀ {X} → Action X
⊥p = record { L = λ _ → ⊥ ; act = λ z → ⊥-elim z }
  
mapP : ∀ {X Y} → (X → Y) → Action X → Action Y
mapP f A = record { L = Action.L A ; act = λ x → f (Action.act A x) }

_∨_ : ∀ {X} → Action X → Action X → Action X
_∨_ {X} A B = record { L = λ w → A.L w ⊎ B.L w ; act = act }
  where
    module A = Action(A)
    module B = Action(B)

    act : ∀ {w} → A.L w ⊎ B.L w → X
    act (inj₁ x) = A.act x
    act (inj₂ y) = B.act y

_+_ : ∀ {X Y} → Action X → Action Y → Action (X ⊎ Y)
A + B = mapP inj₁ A ∨ mapP inj₂ B

_∧_ : ∀ {X Y} → Action X → Action Y → Action (X × Y)
_∧_ {X} A B = record { L = λ w → A.L w × B.L w ; act = λ x → (A.act (proj₁ x)) , B.act (proj₂ x) }
  where
    module A = Action(A)
    module B = Action(B)

_∧'_ : 
