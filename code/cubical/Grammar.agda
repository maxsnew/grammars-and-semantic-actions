module Grammar where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Instances.Sets

open Category
open Functor

private
  variable
    ℓ' ℓ'' ℓ''' ℓ'''' ℓx ℓy ℓa ℓb ℓg ℓg' ℓh ℓh' : Level

module _ (𝓐 : Set ℓ) where
  String = List 𝓐

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] w₁ ++ w₂ ≡ w

  module _ (ℓ' : Level) where
    -- GRAMMAR : Category (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
    -- GRAMMAR = PowerCategory String (SET ℓ')

    Grammar : Type _
    Grammar = String → Type ℓ'

    -- Total parser, parses every string
    Parser : (g : Grammar) → Type _
    Parser g = (w : String) → g w

    -- Discrete : Functor (SET ℓ') GRAMMAR
    -- Discrete .F-ob X w = X
    -- Discrete .F-hom f w x = f x
    -- Discrete .F-id = refl
    -- Discrete .F-seq f g = refl

    -- An action over X can be equivalently defined as an object of
    -- - Grammar ^ X
    -- - Grammar / Δ X
    Action : ∀ {ℓ''} (X : Type ℓ'') → Type _
    Action X = X → Grammar

    module _ {ℓ''} {X : Type ℓ''} where
      Actor : (A : Action X) → Type _
      Actor A = (w : String) → Σ[ x ∈ X ] A x w

      Actionᴰ : ∀ {ℓ'''} (Y : X → Type ℓ''') → Type _
      Actionᴰ Y = {x : X} → Action (Y x)

  module _ where
    ¬ : Grammar ℓ' → Grammar ℓ'
    ¬ g w = g w → ⊥

    ε : Grammar ℓ
    ε a = a ≡ []

    _*_ : Grammar ℓ' → Grammar ℓ'' → Grammar (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    (g₁ * g₂) w = Σ[ s ∈ Splitting w ] g₁ (s .fst .fst) × g₂ (s .fst .snd)

    Σ* : ∀ {X : Type ℓ''} {Y : X → Type ℓ'''}
           (A : Action ℓa X) (B : Actionᴰ ℓb Y)
           → Action (ℓ-max (ℓ-max ℓ ℓa) ℓb) (Σ[ x ∈ X ] Y x)
    Σ* {X = X}{Y = Y} A B (x , y) w = Σ[ s ∈ Splitting w ] A x (s .fst .fst) × B y (s .fst .snd)

    *Σ : ∀ {X : Type ℓ''} {Y : X → Type ℓ'''}
           (A : Action ℓa X) (B : Actionᴰ ℓb Y)
           → Action (ℓ-max (ℓ-max ℓ ℓa) ℓb) (Σ[ x ∈ X ] Y x)
    *Σ {X = X}{Y = Y} A B (x , y) w = Σ[ s ∈ Splitting w ] A x (s .fst .snd) × B y (s .fst .fst)

    _-*_ : Grammar ℓ' → Grammar ℓ'' → Grammar (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    (g₁ -* g₂) w = (wp : String) → g₁ wp → g₂ (wp ++ w)

    _-*A_ : {X : Type ℓx}{Y : Type ℓy}
          → Action ℓa X → Action ℓb Y
          → Action _ (X → Y)
    (A -*A B) f w = ∀ {x} (wp : String) → A x wp → B (f x) (wp ++ w)

    Πp : ∀ {X : Type ℓ''} {Y : X → Type ℓ'''}
           (A : Action ℓa X) (B : Actionᴰ ℓb Y)
           → Action _ ((x : X) → Y x)
    Πp A B f w = ∀ {x} → (wp : String) → A x wp → B (f x) (wp ++ w)

    Πs : ∀ {X : Type ℓ''} {Y : X → Type ℓ'''}
           (A : Action ℓa X) (B : Actionᴰ ℓb Y)
           → Action _ ((x : X) → Y x)
    Πs A B f w = ∀ {x} → (ws : String) → A x ws → B (f x) (w ++ ws)

    _*-_ : Grammar ℓ' → Grammar ℓ'' → Grammar (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    (g₂ *- g₁) w = (ws : String) → g₁ w → g₂ (w ++ ws)

    _*-A_ : {X : Type ℓx}{Y : Type ℓy}
          → Action ℓa Y → Action ℓb X
          → Action _ (X → Y)
    (B *-A A) f w = ∀ {x} (ws : String) → A x ws → B (f x) (w ++ ws)

    y : 𝓐 → Grammar ℓ
    y c w = c ∷ [] ≡ w

    ∂l : 𝓐 → Grammar ℓ' → Grammar (ℓ-max ℓ ℓ')
    ∂l c g = y c -* g

    ∂r : 𝓐 → Grammar ℓ' → Grammar (ℓ-max ℓ ℓ')
    ∂r c g = g *- y c

    ⊤g : Grammar ℓ-zero
    ⊤g w = Unit

    _⊎g_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
    (g ⊎g h) w = g w ⊎ h w

    _⊎A_ : {X : Type ℓx}{Y : Type ℓy}
          → Action ℓa X → Action ℓb Y
          → Action (ℓ-max ℓa ℓb) (X ⊎ Y)
    _⊎A_ {ℓa = ℓa}{ℓb = ℓb} A B (inl x) w = Lift {ℓa}{ℓb} (A x w)
    _⊎A_ {ℓa = ℓa}{ℓb = ℓb} A B (inr y) w = Lift {ℓb}{ℓa} (B y w)

    Unambiguous : Grammar ℓ' → Type (ℓ-max ℓ ℓ')
    Unambiguous g = ∀ w → isProp (g w)

    UnderlyingGrammar : (X : Type ℓ') → Action ℓa X → Grammar (ℓ-max ℓ' ℓa)
    UnderlyingGrammar X A w = Σ[ x ∈ X ] A x w

    PartialG DecG : Grammar ℓ' → Grammar ℓ'

    PartialG g = g ⊎g ⊤g
    DecG g = g ⊎g (¬ g)

    SemiParser DecParser : Grammar ℓ' → Type _

    SemiParser g = Parser _ (PartialG g)
    DecParser g = Parser _ (DecG g)

-- Regexp
  -- data RE {ℓ'} : (B : Set ℓ') → Set (ℓ-max ℓ (ℓ-suc ℓ')) where
  --   Yo : 𝓐 → RE Unit*
  --   ϵ    : RE Unit*
  --   _⨾_ : ∀ {B B' : Set ℓ'} → RE B → RE B' → RE (B × B')
  --   zero : RE ⊥*
  --   _||_ : ∀ {B B' : Set ℓ'} → RE B → RE B' → RE (B ⊎ B')
  --   _⋆ : ∀ {B : Set ℓ'} → RE B → RE (List B)
  --   mapRE : ∀ {B B' : Set ℓ'} → (B → B') → RE B → RE B'

  -- -- CFE
  -- module CFE {ℓ' : Level} where
  --   data CFE : (Γ : List (Type ℓ')) (B : Type ℓ') → Set ((ℓ-max ℓ (ℓ-suc ℓ'))) where
  --     Yo : ∀ {Γ} → 𝓐 → CFE Γ Unit*
  --     ϵ    : ∀ {Γ} → CFE Γ Unit*
  --     _⨾_ : ∀ {Γ}{B B'} → CFE Γ B → CFE Γ B' → CFE Γ (B × B')
  --     zero : ∀ {Γ} → CFE Γ ⊥*
  --     _||_ : ∀ {Γ B B'} → CFE Γ B → CFE Γ B' → CFE Γ (B ⊎ B')

  --     μ   : ∀ {Γ B} → CFE (B ∷ Γ) B → CFE Γ B
  --     var : ∀ {Γ} → (x : Fin (length Γ)) → CFE Γ (lookup Γ x)

  --     mapCFE : ∀ {Γ B B'} → (B → B') → CFE Γ B → CFE Γ B'

  -- module CSE {ℓ' : Level} where
  --   -- "context sensitive expressions" a bit of a misnomer tbh
  --   data CSE : (Γ : List (Type ℓ')) (B : Type ℓ') → Set ((ℓ-max ℓ (ℓ-suc ℓ'))) where
  --     Yo : ∀ {Γ} → 𝓐 → CSE Γ Unit*
  --     ϵ    : ∀ {Γ} → CSE Γ Unit*
  --     _⨾_ : ∀ {Γ B}{B' : B → _} → CSE Γ B → ((b : B) → CSE Γ (B' b)) → CSE Γ (Σ[ b ∈ B ] (B' b))
  --     zero : ∀ {Γ} → CSE Γ ⊥*
  --     _||_ : ∀ {Γ B B'} → CSE Γ B → CSE Γ B' → CSE Γ (B ⊎ B')

  --     μ   : ∀ {Γ B} → CSE (B ∷ Γ) B → CSE Γ B
  --     var : ∀ {Γ} → (x : Fin (length Γ)) → CSE Γ (lookup Γ x)

  --     mapCSE : ∀ {Γ B B'} → (B → B') → CSE Γ B → CSE Γ B'

