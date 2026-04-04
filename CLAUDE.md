# Intrinsic Verification of Parsers and Formal Grammar Theory in Dependent Lambek Calculus

## Overview

This repository is the Cubical Agda formalization accompanying the PLDI 2025 paper by Steven Schaefer, Nathan Varner, Pedro Henrique Azevedo de Amorim, and Max S. New. It implements **Dependent Lambek Calculus (Lambek^D)**, a domain-specific dependent type theory for verified parsing and formal grammar theory. Linear types serve as a syntax for formal grammars, and parsers are written as linear terms. The linear typing restriction provides intrinsic verification: a parser yields only valid parse trees for the input string.

The implementation is a **shallow embedding** in Cubical Agda: rather than formalizing a syntax for Lambek^D, the code defines the constructs of the denotational semantics and programs directly with the denotations.

## Key Concepts

### Core Encoding
- **Grammar**: `String → Type ℓ` — a formal grammar maps strings to types of parse trees (`Grammar.Base`)
- **String**: `List ⟨ Alphabet ⟩` where `Alphabet : hSet ℓ-zero` — strings are lists over a fixed finite alphabet (`String.Base`)
- **Term (Parse Transformer)**: `A ⊢ B` means `∀ (w : String) → A w → B w` — a function mapping parses of `A` to parses of `B` over the same string (`Term.Base`)
- **Parser**: Choice of a type `B` disjoint from `A` plus a function `string ⊸ A ⊕ B` (`Parser.Base`)

### Linear Type Connectives (in `Grammar/`)
- **Concatenation** `A ⊗ B`: string splits into two parts, left parsed by A, right by B (`Grammar.LinearProduct.Base`)
- **Epsilon** `ε`: matches only the empty string (`Grammar.Epsilon.Base`)
- **Literal** `＂ c ＂`: matches single character c (`Grammar.Literal.Base`)
- **Sum** `A ⊕ B` / `⊕ᴰ`: disjunction / indexed disjunction (`Grammar.Sum.*`)
- **Product** `A & B` / `&ᴰ`: conjunction / indexed conjunction (`Grammar.Product.*`)
- **Linear Function** `A ⊸ B`: linear implication (`Grammar.LinearFunction.Base`)
- **Bottom** `⊥`: empty grammar (`Grammar.Bottom.Base`)
- **Top** `⊤`: terminal grammar (`Grammar.Top.Base`)
- **Kleene Star** `A *`: inductive linear type for repetition (`Grammar.KleeneStar.Inductive.Base`)
- **Indexed Inductive Types** `μ F`: least fixed points of strictly positive functors on grammars (`Grammar.Inductive.Indexed`)

### Important Properties
- **Weak Equivalence** `A ≈ B`: parse transformers exist in both directions (`Grammar.Equivalence.Base`)
- **Strong Equivalence** `A ≅ B`: the round-trips are both identity (`Grammar.Equivalence.Base`)
- **Unambiguous**: at most one parse tree per string (`Grammar.Properties.Base`)
- **Disjoint**: `A & B ⊸ ⊥` — no string is parsed by both A and B (`Grammar.Properties.Base`)

### Axioms (not derivable, postulated)
1. **Distributivity** (Axiom 3.1): additive conjunction distributes over additive disjunction (`Grammar.Distributivity`)
2. **Disjoint Constructors** (Axiom 3.3): constructors of sums are disjoint (`Grammar.Sum.Unambiguous`)
3. **Read** (Axiom 3.4): `read : ↑ (⊤ ⊸ string)` and `string ≅ ⊤` (`Grammar.String.Terminal`)

## Main Results Formalized

1. **Thompson's Construction** (`Thompson/`): For every regular expression `r`, constructs an NFA strongly equivalent to `r`. Each regex constructor has its own submodule in `Thompson.Construction.*`. The overall equivalence is assembled in `Thompson.Equivalence`.

2. **Powerset Construction / Determinization** (`Determinization/`): Given an NFA `N`, constructs a DFA weakly equivalent to it (`Determinization.WeakEquivalence`). Requires states, transitions, and ε-transitions of `N` to be finitely ordered (not just finite sets) to enable deterministic choice.

3. **DFA Parsing** (`Automata.Deterministic`): Constructs a parser for traces of any deterministic automaton by recursion on strings.

4. **Regular Expression Parser** (`Examples.RegexParser`): Combines Thompson + Determinization + DFA parsing.

5. **Dyck Grammar Parser** (`Examples.Dyck`): Balanced parentheses via an infinite-state deterministic automaton, strongly equivalent to the Dyck grammar.

6. **Arithmetic Expression Parser** (`Examples.BinOp`): LL(1) grammar with lookahead automaton, weakly equivalent to the expression grammar.

7. **Turing Machine Encoding** (`Automata.Turing.OneSided.Base`): Uses `Reify` to lift any non-linear predicate on strings to a grammar, demonstrating that Lambek^D can encode recursively enumerable languages.

## Project Layout (`src/`)

| Directory | Description |
|-----------|-------------|
| `String/` | String type (`List ⟨ Alphabet ⟩`), ASCII alphabet, sub-alphabets |
| `Grammar/` | All linear type connectives, properties, equivalences, inductive types (~82 files, the largest module) |
| `Term/` | Parse transformers (`A ⊢ B`), composition, category structure, nullary terms (`↑ A`) |
| `Parser/` | Parser definition (Def 4.6 from paper) |
| `Automata/` | DFA, NFA, deterministic automata, Turing machines — all encoded as grammars |
| `Thompson/` | Thompson's construction: regex → NFA with strong equivalence proof |
| `Determinization/` | Powerset construction: NFA → DFA with weak equivalence proof |
| `Examples/` | Verified parsers (Dyck, BinOp, RegexParser) and Section 2 figures |
| `Cubical/` | Supplementary utilities for the Cubical standard library (quiver reachability, FinSet extras, etc.) |

Entry point: `README.agda` imports all `Everything` modules.

## Build

```bash
cd src && make          # Full build (30+ min, compiles cubical + cubical-categorical-logic deps)
cd src && make litmus   # Quick check: builds only the Grammar submodule
```

- **Library file**: `src/grammar.agda-lib` — depends on `cubical` and `cubical-categorical-logic`
- **Agda flags**: `--cubical --guardedness`
- **Memory**: Makefile allocates 8GB (`+RTS -M8G -RTS`); some modules may need interactive loading in VSCode if memory is tight

## Dependencies

- **cubical**: Cubical Agda standard library (at `~/Cubical` or configured via Agda library paths)
- **cubical-categorical-logic**: Category theory extensions for cubical Agda (at `~/cubical-categorical-logic`)

Both must be installed and registered as Agda libraries.

## Important Caveats

### Combinatory Style
Parse transformers are written point-free using combinators, not with named linear variables as in the paper's syntax. E.g., the paper's `f (a, b) = inl (a ⊗ b)` becomes just `f = inl`. Semantically equivalent but syntactically different.

### Opacity
Most definitions use Agda's `opaque` blocks to control unfolding and reduce typechecking time. Selective `unfolding` is used to enable β-equalities (e.g., for `⊗-intro`, `⊕-elim`, `π₁`/`π₂`, distributivity combinators). This is deliberate: unfoldings are either for axiomatizing primitives or for solving equalities that are derivable within Lambek^D.

### Unsafe Pragmas
- `TERMINATING` in `Grammar.Inductive.HLevels` (`encode`, `isRetract`), `Grammar.Inductive.Indexed` (`recHomo`, `μ-η'`), and `Examples.Benchmark.Dyck` (string generation). Safety justified by the retraction to IW-trees in `Grammar.Inductive.HLevels`.
- `NO_POSITIVITY_CHECK` in `Grammar.Inductive.Indexed`: opacity of `⊗` blocks the checker; would pass if `⊗` were transparent. Also justified by the IW-tree retraction.
- `-WnoUnsupportedIndexedMatch` suppressed throughout: harmless warning for indexed pattern matching in Cubical Agda, suppression recommended by Agda docs.

### Performance
Agda's typechecker acts as the parser runtime, which is slow. No IO interface; inputs are mocked as string literals or generated. Benchmark: verified Dyck parser takes ~1m for 196K-character input (includes ~20s generation time).

## Conventions for Contributors

- The `A ⊢ B` notation is preferred over `↑ (A ⊸ B)` throughout (they are equivalent via `Term≅Element` in `Grammar.LinearFunction.Base`), because it makes associativity/unit laws for composition hold definitionally.
- Non-linear contexts are implicit (managed by Agda); linear contexts are unary (multi-variable contexts use `⊗`).
- `isSetGrammar` proofs (in `Grammar.HLevels.Base`) are provided as side conditions to ensure grammars are set-valued per the denotational semantics.
- Grammars are parameterized by `Type ℓ` rather than `hSet ℓ` for generality; the `isSet` proof is a separate side condition.
