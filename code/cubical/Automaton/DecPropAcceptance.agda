{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automaton.DecPropAcceptance (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
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
    isAcc : Q → DecProp ℓ
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop step : Tag

  TraceTy : (A : DecProp ℓ) → (q : Q) → Functor Q (ℓ-suc ℓ)
  TraceTy A q =
    ⊕e Tag λ {
      stop → ⊕e (isAcc q ≡ A) λ acc → k ε
    ; step → ⊕e ⟨ Alphabet ⟩ (λ c → ⊗e (k (literal* c)) (Var (δ q c)))
    }

  Trace : (A : DecProp ℓ) → (q : Q) → Grammar (ℓ-suc ℓ)
  Trace A = μ (TraceTy A)

  STOP : ∀ {q} → ε ⊢ Trace (isAcc q) q
  STOP =
    roll
    ∘g ⊕ᴰ-in stop
    ∘g ⊕ᴰ-in refl
    ∘g liftG

  STEP :
    ∀ {A : DecProp ℓ} →
    {q : Q} →
    (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace A (δ q c) ⊢ Trace A q
  STEP c = roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace DecPropUnit* init

  ParseAlg : (Q → Grammar ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
  ParseAlg g = Algebra (TraceTy DecPropUnit*) g

  open StrongEquivalence
  parseAlg : Algebra (*Ty char) λ _ → &[ q ∈ Q ] ⊕[ A ∈ DecProp ℓ ] Trace A q
  parseAlg _ = ⊕ᴰ-elim (λ {
    nil → &ᴰ-in (λ q →
      ⊕ᴰ-in (isAcc q) ∘g
      roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in refl ∘g liftG ∘g lowerG ∘g lowerG)
    ; cons → &ᴰ-in (λ q → (
      ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun
          ∘g id ,⊗ &ᴰ-π (δ q c))
      ∘g ⊕ᴰ-distL .fun)
      ∘g lowerG ,⊗ lowerG) })

  parse : string ⊢ &[ q ∈ Q ] ⊕[ A ∈ DecProp ℓ ] Trace A q
  parse = rec (*Ty char) parseAlg _

  parseInit : string ⊢ ⊕[ A ∈ DecProp ℓ ] Trace A init
  parseInit = &ᴰ-π init ∘g parse

  printAlg : ∀ A → Algebra (TraceTy A) (λ _ → string)
  printAlg A q = ⊕ᴰ-elim λ {
      stop → ⊕ᴰ-elim λ qAcc≡A → NIL ∘g lowerG
    ; step → CONS ∘g ⊕ᴰ-elim (λ { c → ⊕ᴰ-in c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG }) }

  print : ∀ A → (q : Q) → Trace A q ⊢ string
  print A q = rec (TraceTy A) (printAlg A) q

  ⊕ᴰAlg : ∀ A → Algebra (TraceTy A) (λ q → ⊕[ A ∈ DecProp ℓ ] Trace A q)
  ⊕ᴰAlg A q = ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { qAcc≡A → ⊕ᴰ-in A ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in qAcc≡A })
    ; step → ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun ∘g (lowerG ∘g lowerG) ,⊗ lowerG) })

  Trace≅string : (q : Q) → StrongEquivalence (⊕[ A ∈ DecProp ℓ ] Trace A q) string
  Trace≅string q .fun = ⊕ᴰ-elim (λ A → print A q)
  Trace≅string q .inv = &ᴰ-π q ∘g parse
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = isRetract
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      isRetract : &ᴰ-π q ∘g parse ∘g ⊕ᴰ-elim (λ A → print A q) ≡ id
      isRetract = ⊕ᴰ≡ _ _ λ A →
        ind'
          (TraceTy A)
          (⊕ᴰAlg A)
          ((λ q'  → &ᴰ-π q' ∘g parse ∘g print A q') ,
          λ q' → ⊕ᴰ≡ _ _ (λ {
            stop → funExt λ w → funExt λ {
              (x , p) →
                J {x = isAcc q'}
                  (λ y q →
                    (isAcc q' , μ.roll w (stop , (λ _ → isAcc q') , lift (p .lower)))
                    ≡
                    (y , μ.roll w (stop , q , lift (p .lower)))
                    )
                  refl
                  x
              }
          ; step → ⊕ᴰ≡ _ _ (λ { c → refl })
          }))
          ((λ q' → ⊕ᴰ-in A) ,
          λ q' → ⊕ᴰ≡ _ _ λ {
            stop → funExt (λ w → funExt λ {
              (x , p) → refl})
          ; step → refl })
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ A ∈ DecProp ℓ ] Trace A q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym≅ (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ A q → unambiguous (Trace A q)
  unambiguous-Trace A q = unambiguous⊕ᴰ isSetDecProp (unambiguous-⊕Trace q) A

  ε-parse-unique :
    ∀ q →
    (e : ε ⊢ ⊕[ A ∈ DecProp ℓ ] Trace A q) →
    e ≡ ⊕ᴰ-in (isAcc q) ∘g STOP
  ε-parse-unique q e =
    unambiguous-⊕Trace q e (⊕ᴰ-in (isAcc q) ∘g STOP)

  Parse&Trace :
    ∀ A → Parse & Trace A init ⊢ ⊕[ x ∈ A ≡ DecPropUnit* ] Parse
  Parse&Trace A =
    map⊕ᴰ (λ _ → &-π₁)
    ∘g ⊕ᴰ-fst≡ _ _ _ _ (sym e≡f)
    where
    e f : Parse & Trace A init ⊢ ⊕[ A' ∈ DecProp ℓ ] Trace A' init
    e = ⊕ᴰ-in DecPropUnit* ∘g &-π₁
    f = ⊕ᴰ-in A ∘g &-π₂

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
    acc : Q → DecProp ℓ
    null : DecProp ℓ
    δ₀ : FreeInitial Q → ⟨ Alphabet ⟩ → Maybe Q

  open DeterministicAutomaton

  Aut : DeterministicAutomaton (Maybe (FreeInitial Q))
  Aut .init = just initial
  Aut .isAcc nothing = DecProp⊥*
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
    Type (ℓ-max (ℓ-suc ℓ) ℓ')
  AutAlg g = ParseAlg Aut (implicitFailCarrier g)

  AutAlg-nothing :
    {g : FreeInitial Q → Grammar ℓ'} →
    ⟦ TraceTy Aut DecPropUnit* nothing ⟧ (implicitFailCarrier g) ⊢ ⊥
  AutAlg-nothing =
    ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim λ x → Empty.rec (DecProp⊥*≢DecPropUnit* x)
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
    Parse Aut & ε ⊢ ⊕[ x ∈ Aut .isAcc (just initial) ≡ DecPropUnit* ] ⊤
  init&ε→nullable =
    map⊕ᴰ (λ _ → ⊤-intro)
    ∘g Parse&Trace Aut (isAcc Aut (init Aut))
    ∘g id ,&p STOP Aut

  ¬NullAut :
    null ≡ DecProp⊥* →
    ⟨ ¬Nullable Parse Aut ⟩
  ¬NullAut ¬null =
    ⊕ᴰ-elim (λ null → Empty.rec (DecProp⊥*≢DecPropUnit* (sym ¬null ∙ null)))
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
