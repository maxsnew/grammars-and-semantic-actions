# Dependent Lambek Calculus — Lean 4

## Overview

Lean 4 implementation of **Dependent Lambek Calculus (Lambek^D)**, a domain-specific dependent type theory for verified parsing. Linear types serve as a syntax for formal grammars; parsers are linear terms. The linear typing restriction provides intrinsic verification: a parser yields only valid parse trees for the input string.

This library is intended for writing **verified parsers that actually run**. The long-term goal is to self-host the Lean 4 parser (or at least a substantial fragment). Parsers written in this library should compile to executable code.

## Design Principles

1. **Computability**: Object-level definitions (parsers, grammar transformers) must not use `noncomputable`. We need code that executes, not just typechecks.

2. **Guaranteed termination**: `partial` is not acceptable for object-level definitions. Recursion in the DSL must come with a termination argument (e.g., structural recursion via the `.rec` eliminator from `grammar_inductive`).

3. **Elaborated syntax first**: The `[| ... |]` DSL is the primary interface for writing Lambek^D terms. It is more readable and closely mirrors the paper's presentation. Prefer it over raw combinators or point-free definitions.

4. **Shallow embedding**: Grammars are functions `String → Type`, not inductive syntax. `A ⊢ B` is `∀ w, A w → B w`. The elaborator compiles the linear DSL directly into these semantic values.

5. **Port from Agda**: The Agda formalization (`../src/`) contains the complete grammar theory — automata, Thompson's construction, determinization, Kleene star properties, and verified parsers for Dyck, BinOp, and regular expressions. Porting this theory and these constructions to Lean is a priority. The Lean side currently has the core connectives, categorical structure, elaborator, and tactic infrastructure; the grammar theory and parser examples are the frontier.

## Core Encoding

| Concept | Definition | File |
|---------|-----------|------|
| **Grammar** | `String → Type uGram` | `Core/Base.lean` |
| **String** | `List Alphabet` | `Core/Base.lean` |
| **Splitting** | `{ left, right, eq : left ++ right = w }` | `Core/Base.lean` |
| **Parse Transformer** | `A ⊢ B := ∀ w, A w → B w` | `Core/Connectives.lean` |
| **Alphabet** | `AlphabetStr` typeclass with `Inhabited` + `DecidableEq` | `Core/Base.lean` |

## Linear Type Connectives (`Core/Connectives.lean`)

| Connective | Notation | Lean Type |
|-----------|----------|-----------|
| Tensor | `A ⊗ B` | `{ split : Splitting w, fst : A split.left, snd : B split.right }` |
| Epsilon | `ε` / `Epsilon` | Matches only `[]` |
| Literal | `Literal c` | Matches `[c]` |
| Right linear function | `A ⊸ B` | `∀ w', A w' → B (w' ++ w)` |
| Left linear function | `B ⟜ A` | `∀ w', A w' → B (w ++ w')` |
| Sum | `A ⊕ B` | `Sum (A w) (B w)` |
| Product | `A & B` | `Prod (A w) (B w)` |
| Top | `⊤g` | `ULift PUnit` |
| Bottom | `⊥g` | `ULift PEmpty` |
| Indexed product | `&[x ∈ X] F x` | `∀ x, F x w` |
| Indexed coproduct | `⊕[x ∈ X] F x` | `Σ x, F x w` |
| Kleene star | `A *` | Inductive: `nil` + `cons` |

## The Ordered Linear Elaborator (`Elab/`)

The main way to write Lambek^D terms. The `[| ... |]` macro compiles ordered linear terms with named variables into the denotational semantics:

```lean
-- Multi-pattern tensor flattening
def assocR (A B C : Grammar) : A ⊗ (B ⊗ C) ⊢ A ⊗ (B ⊗ C) :=
  [| a b c => (a, (b, c)) |]

-- Right lambda + application
def curryR (A B C : Grammar) : (A ⊗ B) ⊸ C ⊢ B ⊸ (A ⊸ C) :=
  [| g => fun (b : B) => fun (a : A) => g (a, b) |]

-- Case analysis
def distribute (A B C : Grammar) : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C) :=
  [| a bc => case bc of | inl b => inl (a, b) | inr c => inr (a, c) |]

-- Escape hatch to Lean-level function
def chain (A B C : Grammar) (f : A ⊢ B) (g : B ⊢ C) : A ⊢ C :=
  [| x => #[g] (#[f] x) |]
```

### Linearity Enforcement

The elaborator tracks an **ordered linear context** (`OrderedCtx`). It enforces:
- **No contraction**: Each variable used exactly once
- **No weakening**: No unused variables
- **No exchange**: Variables consumed left-to-right in the string

### Application Resolution

`f a` is resolved by variable position:
- `a` LEFT of `f` → **right-app** via `⊸`
- `f` LEFT of `a` → **left-app** via `⟜`

### grammar_inductive

Declares inductive grammar types indexed by strings:

```lean
grammar_inductive Dyck where
  | nil : Epsilon
  | cons : Literal Paren.lparen ⊗ Dyck ⊗ Literal Paren.rparen ⊗ Dyck
```

Constructor types like `A ⊗ B ⊗ C` are internally **tensor-flattened** to avoid Lean's nested inductive restrictions. Constructors are usable directly in `[| ... |]`.

### Structural Recursion (`rec ... as ... of`)

```lean
def append : Dyck ⊗ Dyck ⊢ Dyck :=
  [| d d' => rec d as append of
     | nil x => let () = x in d'
     | cons lp e rp e' => cons lp e rp (append e')
   |]
```

Uses the `.rec` eliminator from `grammar_inductive`. IHs introduced automatically for recursive fields. This is the mechanism for guaranteed-terminating recursion — no `partial` needed.

## Tactics

| Tactic | Purpose |
|--------|---------|
| `splitting_cases` | Eliminates `Splitting`/`PLift`/`ULift` + `subst` equalities |
| `grammar_ext` | Morphism equality by `funext` + structure elimination |
| `grammar_simp` | Simp set: string, composition, bifunctor, β/η lemmas |

## Project Layout

```
Lean/
├── lakefile.toml                  # Build config (mathlib + Canonical)
├── LambekD.lean                   # Root import
├── LambekD/
│   ├── Core/
│   │   ├── Base.lean              # Grammar, String, Splitting, AlphabetStr
│   │   ├── Connectives.lean       # All linear connectives + notation
│   │   └── Defs.lean              # gId, gComp, composition laws
│   ├── Grammar/
│   │   ├── Cat.lean               # Category instance (via CategoryTheory.Pi)
│   │   ├── Tensor.lean            # Bifunctoriality, associator, unitors, coherence
│   │   ├── Sum.lean               # Injections, case elimination, β/η
│   │   ├── Product.lean           # Projections, pairing, diagonal, β/η
│   │   ├── FunctionR.lean         # ⊸ intro/app/β/η
│   │   ├── FunctionL.lean         # ⟜ intro/app/β/η
│   │   ├── Epsilon.lean           # εIntro
│   │   ├── Top.lean               # topIntro, uniqueness
│   │   ├── Bottom.lean            # botElim, uniqueness
│   │   ├── Equivalence.lean       # Weak (≈g) and strong (≅g) equivalence
│   │   ├── Monoidal.lean          # MonoidalCategory instance
│   │   ├── MonoidalClosed.lean    # MonoidalBiclosed instance
│   │   ├── Distributivity.lean    # Tensor distributes over sum
│   │   ├── Properties/Base.lean   # Unambiguous, Disjoint
│   │   ├── KleeneStar/Base.lean   # Inductive Kleene star, foldStarR
│   │   └── String/
│   │       ├── Base.lean          # char, string, exact, mkString
│   │       └── Terminal.lean      # String as terminal grammar
│   ├── Elab/
│   │   ├── Base.lean              # OrderedVar, OrderedCtx, Alias, ElabConfig
│   │   ├── Syntax.lean            # Surface syntax (gterm, gpat categories)
│   │   ├── Match.lean             # Grammar type decomposition
│   │   ├── Util.lean              # Context analysis, findSplit, string proofs
│   │   ├── Elaborator.lean        # Main elaboration: gterm → Lean Expr
│   │   ├── Inductive.lean         # grammar_inductive command + rec/fold
│   │   └── IDE.lean               # Linear context display for hover info
│   ├── Tactic/
│   │   ├── Base.lean              # splitting_cases, grammar_ext tactics
│   │   └── Simp.lean              # grammar_simp simp set
│   ├── CategoryTheory/
│   │   └── Biclosed/Monoidal.lean # Biclosed monoidal category class
│   └── Examples/
│       └── ElabExamples.lean      # Comprehensive elaborator test suite
```

## Build

```bash
cd Lean && lake build
```

**Dependencies**: mathlib (rev `308445d`), Canonical (chasenorman)
**Options**: `autoImplicit = false`, `pp.unicode.fun = true`

## Common Patterns

### Adding a New Connective
1. Define in `Core/Connectives.lean` (or new `Grammar/` file)
2. Add intro/elim rules with β/η laws
3. Register lemmas in `grammar_simp` (`Tactic/Simp.lean`)
4. For `[| ... |]` support: syntax in `Elab/Syntax.lean`, matching in `Elab/Match.lean`, cases in `Elab/Elaborator.lean`

### Adding a New Elaborator Form
1. Syntax in `gterm` category (`Elab/Syntax.lean`)
2. Case in `elaborateOrderedTerm` (`Elab/Elaborator.lean`)
3. Tests in `Examples/ElabExamples.lean`
