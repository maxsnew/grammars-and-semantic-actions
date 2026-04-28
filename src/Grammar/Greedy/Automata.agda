open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Greedy.Automata (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Grammar.Greedy.Base Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.External.String.Tiny Alphabet
open import Automata.Deterministic Alphabet
open import Term Alphabet
open import Parser Alphabet

private
  variable
    ℓ : Level

module _ {Q : Type ℓ} (D : DeterministicAutomaton Q) where
  open module D = DeterministicAutomaton D

  private
    state : Q → Grammar _
    state q = ⊕[ b ∈ Bool ] Trace b q

  open StrongEquivalence

  δ* : Q → String → Q
  δ* q [] = q
  δ* q (c ∷ w) = δ* (δ q c) w

  STEP* : ∀ b q w → ⌈ w ⌉ ⊗ Trace b (δ* q w) ⊢ Trace b q
  STEP* b q []      = ⊗-unit-l
  STEP* b q (c ∷ w) =
    STEP c b q
    ∘g id ,⊗ STEP* b (δ q c) w
    ∘g ⊗-assoc⁻

  opaque
    unfolding _⟜_ _&_ _⊗_ ⊥
    -- TODO make this disjointness proof internal
    ⟜-Trace-disj : ∀ (q : Q) (w : String)
      → (Trace true q ⟜ ⌈ w ⌉) & Trace false (δ* q w) ⊢ ⊥
    ⟜-Trace-disj q w u (f , tf)  =
      AccTraceParser q .Parser.disj (w ++ u)
        ( f w (mk⌈⌉ w)
        , STEP* false q w (w ++ u)
            (((w , u) , Eq.refl) , (mk⌈⌉ w , tf))
        )

  private
    Trace-split-at-⌈⌉ : ∀ b q w
      → (⌈ w ⌉ ⊗ ⊤) & Trace b q ⊢ ⌈ w ⌉ ⊗ Trace b (δ* q w)
    Trace-split-at-⌈⌉ true q w =
      ⊕ᴰ-elim (λ where
        true  → π₁
        false →
          ⊥-elim
          ∘g AccTraceParser q .Parser.disj
          ∘g &-swap
          ∘g STEP* false q w ,&p id)
      ∘g &⊕ᴰ-distL≅ .fun
      ∘g ⊕ᴰ-distR .fun ,&p id
      ∘g (id ,⊗ (π (δ* q w) ∘g parse ∘g string-intro)) ,&p id
    Trace-split-at-⌈⌉ false q w =
      ⊕ᴰ-elim (λ where
        true  →
          ⊥-elim
          ∘g AccTraceParser q .Parser.disj
          ∘g STEP* true q w ,&p id
        false → π₁)
      ∘g &⊕ᴰ-distL≅ .fun
      ∘g ⊕ᴰ-distR .fun ,&p id
      ∘g (id ,⊗ (π (δ* q w) ∘g parse ∘g string-intro)) ,&p id

  private
    trace-true→Greedy : (q : Q) → Trace true q ⊢ Greedy (Trace true q)
    trace-true→Greedy q =
      ⊕ᴰ-elim (λ w →
        σ w
        ∘g id ,⊗ ⇒-intro (¬Nullable⊗l ¬Nullable-&char+)
        ∘g ⊗-unit-r⁻)
      ∘g &⊕ᴰ-distL≅ .fun
      ∘g ⊤→⊕⌈⌉ ,&p id
      ∘g ⊤-intro ,& id

    extend-GreedyCompl : (q : Q) →
      (GreedyCompl (Trace true q) ⊗ char) & Trace false q
      ⊢ GreedyCompl (Trace true q)
    extend-GreedyCompl q = ⇒-intro
      (⊕-elim
         (AccTraceParser q .Parser.disj ∘g &-swap ∘g π₂ ∘g &-assoc⁻)
         (⊥⊗
          ∘g (⇒-app ∘g id ,&p (id ,⊗ ⊤-intro)) ,⊗ id
          ∘g char-⊗&-distR⁻
          ∘g id ,&p ⊗-assoc
          ∘g (π₁ ∘g π₁) ,& π₂)
       ∘g &⊕-distL
       ∘g id ,&p (
         (⊗-unit-r ,⊕p id)
         ∘g ⊗⊕-distL
         ∘g id ,⊗ (unroll-string≅' .fun ∘g string-intro)))

    extend-Greedy : (q : Q) →
      (Greedy (Trace true q) ⊗ char) & Trace false q
      ⊢ Greedy (Trace true q)
    extend-Greedy q =
      ⊕ᴰ-elim (λ w → σ w ∘g body w)
      ∘g &⊕ᴰ-distL≅ .fun
      ∘g ⊕ᴰ-distL .fun ,&p id
      where
      -- Build the evidence that there is no extended parse found after
      -- witnessing that the automaton ends in a fail state for the
      -- entire string
      Nbuilder : ∀ (w : String) →
          ((¬G (((Trace true q ⟜ ⌈ w ⌉) & char +) ⊗ ⊤)) ⊗ char)
        & Trace false (δ* q w)
        ⊢ ¬G (((Trace true q ⟜ ⌈ w ⌉) & char +) ⊗ ⊤)
      Nbuilder w = ⇒-intro
        (⊕-elim
           (⟜-Trace-disj q w
            ∘g π₁ ,&p id
            ∘g &-swap
            ∘g π₂
            ∘g &-assoc⁻)
           (⊥⊗
            ∘g (⇒-app ∘g id ,&p (id ,⊗ ⊤-intro)) ,⊗ id
            ∘g char-⊗&-distR⁻
            ∘g id ,&p ⊗-assoc
            ∘g (π₁ ∘g π₁) ,& π₂)
         ∘g &⊕-distL
         ∘g id ,&p (
           (⊗-unit-r ,⊕p id)
           ∘g ⊗⊕-distL
           ∘g id ,⊗ (unroll-string≅' .fun ∘g string-intro)))

      body : ∀ (w : String) →
          (((⌈ w ⌉ & Trace true q) ⊗ ¬G (((Trace true q ⟜ ⌈ w ⌉) & char +) ⊗ ⊤))
            ⊗ char)
        & Trace false q
        ⊢ (⌈ w ⌉ & Trace true q) ⊗ ¬G (((Trace true q ⟜ ⌈ w ⌉) & char +) ⊗ ⊤)
      body w =
        id ,⊗ Nbuilder w
        ∘g ⌈⌉-prefix-push {w = w} π₁
        ∘g id ,&p Trace-split-at-⌈⌉ false q w
        ∘g π₁ ,& (((π₁ ,⊗ ⊤-intro) ∘g π₁) ,& π₂)
        ∘g ⊗-assoc⁻ ,&p id

  parseGreedy' : (q : Q) →
    string ⊢ (Greedy (Trace true q) ⊕ GreedyCompl (Trace true q)) & state q
  parseGreedy' q = fold*l char
    (⊕ᴰ-elim (λ {
        true → inl ∘g trace-true→Greedy q ∘g π₂
      ; false → inr ∘g ⇒-intro (
          (⊕-elim
            ((AccTraceParser q .Parser.disj ∘g &-swap) ∘g π₁ ∘g &-assoc)
            ((¬Nullable⊗r ¬Nullable-char+ ∘g &-swap) ∘g π₂)
          ∘g &⊕-distL
          ∘g id ,&p
            (&⊕-distR ∘g
              ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL
               ∘g id ,⊗ (unroll-string≅ .fun ∘g string-intro)) ,&p id))
          ∘g &-swap ∘g &-assoc ∘g &-swap)
     }) ,& map⊕ᴰ (λ _ → π₂)
      ∘g &⊕ᴰ-distR≅ .fun
      ∘g id ,& (π q ∘g parse ∘g string-intro))
    (⊕ᴰ-elim (λ {
         true → (inl ∘g trace-true→Greedy q ∘g π₂) ,& (σ true ∘g π₂)
       ; false →
           (⊕-elim
              (inl ∘g extend-Greedy q)
              (inr ∘g extend-GreedyCompl q)
            ∘g &⊕-distR ∘g ⊗⊕-distR ,&p id)
           ,& (σ false ∘g π₂)
      })
     ∘g &⊕ᴰ-distR≅ .fun
     ∘g id ,&p (⊕ᴰ-elim (λ b → STEP'char b q) ∘g ⊕ᴰ-distL .fun)
     ∘g ⊗&-distR)

  parseGreedy : (q : Q) → string ⊢ (Greedy (Trace true q) ⊕ GreedyCompl (Trace true q))
  parseGreedy q = π₁ ∘g parseGreedy' q

  GreedyParser : ∀ q → Parser (Greedy (Trace true q)) (GreedyCompl (Trace true q))
  GreedyParser q .Parser.disj = disjointGreedy-GreedyCompl (Trace true q)
  GreedyParser q .Parser.fun = parseGreedy q
