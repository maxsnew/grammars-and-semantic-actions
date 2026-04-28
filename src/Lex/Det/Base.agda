{-# OPTIONS -WnoUnsupportedIndexedMatch --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Lex.Det.Base
  (Alphabet : hSet ℓ-zero)
  where

open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as MaybeD using (Maybe ; nothing ; just)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Grammar Alphabet hiding (Δ)
open import Grammar.Maybe.Base Alphabet
open import Grammar.SemanticAction Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.Greedy.Base Alphabet
import Grammar.Greedy.Automata Alphabet as GA

open import Parser.Base Alphabet
import Parser.RecursiveDescent Alphabet as RD
open RD hiding (Parser)

open import Automata.Deterministic Alphabet
open import Automata.Implicit Alphabet
open import Automata.Implicit.AsDeterministic Alphabet

open import Term Alphabet

open StrongEquivalence

private
  variable
    ℓ : Level

module _ (M : ImplicitDeterministicAutomaton ℓ-zero) where
  private
    DM : DeterministicAutomaton _
    DM = IDA→DA M

  open DeterministicAutomaton DM
    public
    using ()
    renaming (Trace to TraceDA ; init to q₀DA ; print to printDA)

  matchExact-IDA : string ⊢ Maybe (TraceDA true q₀DA)
  matchExact-IDA =
    ⊕-elim just nothing
    ∘g DeterministicAutomaton.AccTraceParser DM q₀DA .Parser.fun

  longestMatch-IDA : string ⊢ Maybe (TraceDA true q₀DA ⊗ string)
  longestMatch-IDA =
    ⊕-elim
      (just ∘g (id ,⊗ string-intro) ∘g Greedy→leftmost _)
      nothing
    ∘g GA.parseGreedy DM q₀DA

  ¬Nullable-TraceDA-init :
    M .ImplicitDeterministicAutomaton.null ≡ false →
    ⟨ ¬Nullable (TraceDA true q₀DA) ⟩
  ¬Nullable-TraceDA-init notNull =
    char+→¬Nullable trace-init→char+
    where
    open DeterministicAutomaton DM
      using (Tag ; stop ; step ; TraceTy)

    trace-init→char+ : TraceDA true q₀DA ⊢ char +
    trace-init→char+ =
      ⊕ᴰ-elim per-tag
      ∘g unroll (TraceTy true) q₀DA
      where
      per-tag : (t : Tag) → _ ⊢ char +
      per-tag stop =
        ⊕ᴰ-elim λ where
          (lift x) →
            Empty.rec (true≢false (Eq.eqToPath x ∙ notNull))
      per-tag step =
        ⊕ᴰ-elim λ where
          (lift c) →
            literal→char c ,⊗ string-intro
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG

record LexRule (Token : Type ℓ) : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ) where
  field
    autom  : ImplicitDeterministicAutomaton ℓ-zero
    action : List ⟨ Alphabet ⟩ → MaybeD.Maybe Token

Lexicon : Type ℓ → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
Lexicon Token = List (LexRule Token)

pickAction :
  ∀ {Token : Type ℓ} (rules : Lexicon Token) →
  string ⊢ Maybe (Δ (MaybeD.Maybe Token))
pickAction []        = nothing
pickAction (r ∷ rs)  =
  ⊕-elim
    (just ∘g semact-map (LexRule.action r) semact-string ∘g π₂)
    (pickAction rs ∘g π₂)
  ∘g &⊕-distR
  ∘g matchExact-IDA (LexRule.autom r) ,& id

pickAction-collapse :
  ∀ {X : Type ℓ} → Maybe (Δ X) ⊢ Δ (MaybeD.Maybe X)
pickAction-collapse =
  ⊕-elim
    (semact-map MaybeD.just semact-Δ)
    (semact-pure MaybeD.nothing)

module _ {Token : Type ℓ}
         (UM : ImplicitDeterministicAutomaton ℓ-zero)
         (¬nullTrace : ⟨ ¬Nullable (TraceDA UM true (q₀DA UM)) ⟩)
         (rules : Lexicon Token)
         where

  private
    uR-match : string ⊢ Maybe (TraceDA UM true (q₀DA UM) ⊗ string)
    uR-match = longestMatch-IDA UM

  opaque
    ruleAction :
      TraceDA UM true (q₀DA UM)
      ⊢ Δ (MaybeD.Maybe (MaybeD.Maybe Token))
    ruleAction =
      pickAction-collapse
      ∘g pickAction rules
      ∘g printDA UM true (q₀DA UM)

  private
    X : Grammar ℓ
    X = MaybeLeft (Δ (List Token))

    base : ▷ X & ε ⊢ X
    base =
      just
      ∘g (semact-pure [] ,⊗ string-intro)
      ∘g ⊗-unit-l⁻
      ∘g π₂

    combine : Δ (MaybeD.Maybe (MaybeD.Maybe Token)) ⊗ X ⊢ X
    combine =
      ⊕ᴰ-elim per-case
      ∘g ⊕ᴰ-distL .fun
      where
      per-case : (mmt : MaybeD.Maybe (MaybeD.Maybe Token)) → ⊤ ⊗ X ⊢ X
      per-case MaybeD.nothing = nothing ∘g ⊤-intro
      per-case (MaybeD.just MaybeD.nothing) =
        fmap (Δ-absorb-l ,⊗ id ∘g ⊗-assoc) ∘g Maybe⊗r
      per-case (MaybeD.just (MaybeD.just t)) =
        fmap (semact-map (t ∷_) Δ-absorb-l ,⊗ id ∘g ⊗-assoc)
        ∘g Maybe⊗r

    succeed : ▷ X & (TraceDA UM true (q₀DA UM) ⊗ string) ⊢ X
    succeed =
      combine
      ∘g ruleAction ,⊗ id
      ∘g ▷-app-NE ¬nullTrace
      ∘g &-swap
      ∘g id ,&p (id ,⊗ ⊤-intro)

    iter : ▷ X & (char ⊗ string) ⊢ X
    iter =
      ⊕-elim
        succeed
        (nothing ∘g ⊤-intro)
      ∘g &⊕-distL
      ∘g id ,&p uR-match
      ∘g id ,&p string-intro

    step' : ▷ X & string ⊢ X
    step' =
      ⊕-elim base iter
      ∘g &⊕-distL
      ∘g id ,&p unroll-string≅ .fun

    step : ▷ X ⊢ X
    step = step' ∘g id ,& string-intro

  lexParser : RD.Parser (Δ (List Token))
  lexParser = fixP step

  lex : string ⊢ Maybe (Δ (List Token))
  lex = parse lexParser

  opaque
    unfolding unfoldGrammarDefs
    runLex : List ⟨ Alphabet ⟩ → MaybeD.Maybe (List Token)
    runLex w =
      Sum.rec (λ p → MaybeD.just (fst p))
              (λ _ → MaybeD.nothing)
              (lex w (mkstring w))
