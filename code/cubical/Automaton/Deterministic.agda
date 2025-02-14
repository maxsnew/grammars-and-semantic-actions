{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automaton.Deterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sum hiding (rec; map)
open import Cubical.Data.Maybe as Maybe hiding (rec)
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Product.Properties Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Grammar.SequentialUnambiguity Alphabet
open import Term Alphabet
open import Helper

private
  variable
    ℓ ℓ' : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop step : Tag

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → ⊗e (k (literal* c)) (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

  STOP : ∀ {q} → ε ⊢ Trace (isAcc q) q
  STOP =
    roll
    ∘g ⊕ᴰ-in stop
    ∘g ⊕ᴰ-in (lift (Eq.refl))
    ∘g liftG ∘g liftG

  STEP :
    ∀ {b : Bool} →
    {q : Q} →
    (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace b (δ q c) ⊢ Trace b q
  STEP c = roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace true init

  ParseAlg : (Q → Grammar ℓ') → Type (ℓ-max ℓ ℓ')
  ParseAlg g = Algebra (TraceTy true) g

  open StrongEquivalence
  parseAlg : Algebra (*Ty char) λ _ → &[ q ∈ Q ] ⊕[ b ∈ Bool ] Trace b q
  parseAlg _ = ⊕ᴰ-elim (λ {
    nil → &ᴰ-in (λ q →
      ⊕ᴰ-in (isAcc q) ∘g
      roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) ∘g
      liftG ∘g liftG ∘g lowerG ∘g lowerG)
    ; cons → &ᴰ-in (λ q → (
      ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun
          ∘g id ,⊗ &ᴰ-π (δ q c))
      ∘g ⊕ᴰ-distL .fun)
      ∘g lowerG ,⊗ lowerG) })

  parse : string ⊢ &[ q ∈ Q ] ⊕[ b ∈ Bool ] Trace b q
  parse = rec (*Ty char) parseAlg _

  parseInit : string ⊢ ⊕[ b ∈ Bool ] Trace b init
  parseInit = &ᴰ-π init ∘g parse

  printAlg : ∀ b → Algebra (TraceTy b) (λ _ → string)
  printAlg b q = ⊕ᴰ-elim λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → NIL ∘g lowerG ∘g lowerG })
    ; step → CONS ∘g ⊕ᴰ-elim (λ { (lift c) → ⊕ᴰ-in c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG }) }

  print : ∀ b → (q : Q) → Trace b q ⊢ string
  print b q = rec (TraceTy b) (printAlg b) q

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q = ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) })
    ; step → ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun ∘g (lowerG ∘g lowerG) ,⊗ lowerG) })

  Trace≅string : (q : Q) → StrongEquivalence (⊕[ b ∈ Bool ] Trace b q) string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = &ᴰ-π q ∘g parse
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = isRetract
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      isRetract : &ᴰ-π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      isRetract = ⊕ᴰ≡ _ _ λ b →
        ind'
          (TraceTy b)
          (⊕ᴰAlg b)
          ((λ q'  → &ᴰ-π q' ∘g parse ∘g print b q') ,
          λ q' → ⊕ᴰ≡ _ _ (λ {
            stop → funExt λ w → funExt λ {
              ((lift Eq.refl) , p) → refl}
          ; step → ⊕ᴰ≡ _ _ (λ { (lift c) → refl })
          }))
          ((λ q' → ⊕ᴰ-in b) ,
          λ q' → ⊕ᴰ≡ _ _ λ {
            stop → funExt (λ w → funExt λ {
              ((lift Eq.refl) , p) → refl})
          ; step → refl })
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b

  ε-parse-unique :
    ∀ q →
    (e : ε ⊢ ⊕[ b ∈ Bool ] Trace b q) →
    e ≡ ⊕ᴰ-in (isAcc q) ∘g STOP
  ε-parse-unique q e =
    unambiguous-⊕Trace q e (⊕ᴰ-in (isAcc q) ∘g STOP)

  Parse&Trace :
    ∀ b → Parse & Trace b init ⊢ ⊕[ x ∈ b ≡ true ] Parse
  Parse&Trace b =
    map⊕ᴰ (λ _ → &-π₁)
    ∘g ⊕ᴰ-fst≡ _ _ _ _ (sym e≡f)
    where
    e f : Parse & Trace b init ⊢ ⊕[ b' ∈ Bool ] Trace b' init
    e = ⊕ᴰ-in true ∘g &-π₁
    f = ⊕ᴰ-in b ∘g &-π₂

    e≡f : e ≡ f
    e≡f = unambiguous-⊕Trace init e f

data FreeInitial (Q : Type ℓ) : Type ℓ where
  initial : FreeInitial Q
  ↑_ : Q → FreeInitial Q

module _ (Q : Type ℓ) where
  open Iso
  FreeInitial≅Unit⊎ : Iso (FreeInitial Q) (Unit ⊎ Q)
  FreeInitial≅Unit⊎ .fun initial = inl _
  FreeInitial≅Unit⊎ .fun (↑ q) = inr q
  FreeInitial≅Unit⊎ .inv (inl _) = initial
  FreeInitial≅Unit⊎ .inv (inr q) = ↑ q
  FreeInitial≅Unit⊎ .rightInv (inl _) = refl
  FreeInitial≅Unit⊎ .rightInv (inr _) = refl
  FreeInitial≅Unit⊎ .leftInv initial = refl
  FreeInitial≅Unit⊎ .leftInv (↑ _) = refl

-- Automata with a transition function given partially such
-- that unspecified transitions implicitly map to a fail state
-- Further, these have a freely added initial state such that
-- there are no back edges to the initial state
record ImplicitDeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor mkImplicitAut
  field
    acc : Q → Bool
    null : Bool
    δ₀ : FreeInitial Q → ⟨ Alphabet ⟩ → Maybe Q

  open DeterministicAutomaton

  Aut : DeterministicAutomaton (Maybe (FreeInitial Q))
  Aut .init = just initial
  Aut .isAcc nothing = false
  Aut .isAcc (just initial) = null
  Aut .isAcc (just (↑ q)) = acc q
  Aut .δ nothing c = nothing
  Aut .δ (just q) c = map-Maybe ↑_ (δ₀ q c)

  open StrongEquivalence

  implicitFailCarrier :
    (g : (FreeInitial Q) → Grammar ℓ') →
    Maybe (FreeInitial Q) → Grammar ℓ'
  implicitFailCarrier g nothing = ⊥*
  implicitFailCarrier g (just q) = g q

  AutAlg :
    (g : FreeInitial Q → Grammar ℓ') →
    Type {!ℓ-max ℓ ℓ'!}
  AutAlg g = ParseAlg Aut (implicitFailCarrier g)

  AutAlg-nothing :
    {g : FreeInitial Q → Grammar ℓ'} →
    ⟦ TraceTy Aut true nothing ⟧ (implicitFailCarrier g) ⊢ ⊥
  AutAlg-nothing =
    ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim λ {()}
    ; step → ⊕ᴰ-elim (λ _ → ⊗⊥ ∘g id ,⊗ (lowerG ∘g lowerG))
    })

  null≡initAcc :
    null ≡ Aut .isAcc (just initial)
  null≡initAcc = refl

  noMapsIntoInit :
    ∀ (q : Maybe (FreeInitial Q)) →
    (c : ⟨ Alphabet ⟩) →
    (Σ[ q' ∈ Q ] Aut .δ q c ≡ just (↑ q')) ⊎
    (Aut .δ q c ≡ nothing)
  noMapsIntoInit nothing c = inr refl
  noMapsIntoInit (just q) c =
    Maybe.elim
      (λ x →
        (Σ[ q' ∈ Q ] map-Maybe ↑_ x ≡ just (↑ q')) ⊎
        (map-Maybe ↑_ x ≡ nothing)
      )
      (inr refl)
      (λ x → inl (x , refl))
      (δ₀ q c)

  init&ε→nullable :
    Parse Aut & ε ⊢ ⊕[ x ∈ Aut .isAcc (just initial) ≡ true ] ⊤
  init&ε→nullable =
    map⊕ᴰ (λ _ → ⊤-intro)
    ∘g Parse&Trace Aut (isAcc Aut (init Aut))
    ∘g id ,&p STOP Aut

  ¬NullAut :
    null ≡ false →
    ⟨ ¬Nullable Parse Aut ⟩
  ¬NullAut ¬null =
    ⊕ᴰ-elim (λ null → Empty.rec (true≢false (sym null ∙ ¬null)))
    ∘g init&ε→nullable
    ∘g &-swap

  Parse&startsWith→initialTransitionIsJust :
    (c : ⟨ Alphabet ⟩) →
    Parse Aut & startsWith c ⊢
      ⊕[ x ∈ (Σ[ q ∈ Q ] δ₀ initial c ≡ just q) ] ⊤
  Parse&startsWith→initialTransitionIsJust c =
    ⇒-intro⁻ (rec _ the-alg (init Aut))
    where
    the-alg :
      AutAlg (λ q → startsWith c ⇒
        (⊕[ x ∈ (Σ[ q ∈ Q ] δ₀ initial c ≡ just q) ] ⊤)
      )
    the-alg nothing = ⊥-elim ∘g AutAlg-nothing
    the-alg (just initial) =
      {!!}
    the-alg (just (↑ q)) =
      {!!}

  ¬FirstAut :
    (c : ⟨ Alphabet ⟩) →
    δ₀ initial c ≡ nothing →
    ⟨ c ∉First Parse Aut ⟩
  ¬FirstAut c initialTransition =
    ⊕ᴰ-elim (λ (q , δ₀≡) →
      Empty.rec (¬nothing≡just (sym initialTransition ∙ δ₀≡)))
    ∘g Parse&startsWith→initialTransitionIsJust c
    ∘g &-swap
