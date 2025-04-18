# Intrinsic Verification of Parsers and Formal Grammar Theory in Dependent Lambek Calculus

1. [Getting Started](#getting-started)
2. [Claims](#claims)
3. [Project Layout](#project-layout)
3. [Dependent Lambek Calculus in Agda](#dependent-lambek-calculus-in-agda)
5. [Caveats](#caveats)

## Getting Started
### Compiling the Repository
Running `make` from the `src` directory will compile `README.agda` which imports
the entirety of the project. This may take longer than 30 minutes, as it will
also compile the dependencies from `cubical` and `cubical-categorical-logic` if
they are not already built. You may also build `README.agda` interactively by
loading the file with
[agda-mode](https://agda.readthedocs.io/en/v2.7.0.1/tools/emacs-mode.html).

If the compilation of `README.agda` doesn't immediately crash, and you can see
it checking submodules, it is very likely that the there will be no technical
difficulties. We have also included the target `make litmus` which builds only
the `Grammar` submodule as a shorter litmus test to check for issues of
technical compatibility.

#### Memory Requirement

Depending on hardware differences, high memory usage may cause the typechecking process to be killed when checking `Cubical.Categories.Monoidal.Dual` from `cubical-categorical-logic`. This issue was encountered by one artifact reviewer but has not been reproduced by the authors. The issue was then alleviated by switching to VSCode and loading the project interactively.

## Claims

The contributions of this codebase are:
1. A domain-specific language for building intrinsically verified parsers. This comprises the entire repository, but the bulk of language primitives are found in the `Grammar`, `Term`, `Parser`, and `String` modules.
2. A verification of Thompson's construction, given in `Thompson.Equivalence`.
3. A verification of the powerset construction for NFA determinization, given in `Determinization.WeakEquivalence`.
4. Example parsers written in `Lambekᴰ`,
  - A regular expression parser that is implemented by determinizing Thompson's construction, given in `Examples.RegexParser`.
  - A parser for an `LL(0)` grammar of balanced parentheses, given in `Examples.Dyck`.
  - A parser for an `LL(1)` grammar of arithmetic expressions, given in `Examples.BinOp`.

Below, we include the code locations of the specific claims made in the paper.

### Definition 4.1

> Grammars `A` and `B` are __weakly equivalent__ if there exists parse transformers `f : ↑ (A ⊸ B)` and `g : ↑ (B ⊸ A)`. `A` is a __retract__ of `B` if `A` and `B` are weakly equivalent and `λ a . g (f (a)) ≡ λ a . a`. They are __strongly equivalent__ if further the other composition is the identity, i.e., `λ b . f (g (b)) ≡ λ b . b`.

Defined in `Grammar.Equivalence.Base` as `WeakEquivalence` , `isRetractOf`, and `StrongEquivalence`. We frequently use `A ≈ B` as shorthand for `WeakEquivalence A B` and `A ≅ B` as a shorthand for `StrongEquivalence A B`.

### Definition 4.2

> A grammar `A` is __unambiguous__ if for every linear type `B` and `f g : ↑ (B ⊸ A)` then `f ≡ g`.

Defined as `unambiguous` in `Grammar.Properties.Base`. The same file also includes other equivalent characterizations of unambiguity for a grammar `A` that are provable in `Lambekᴰ`:

- The unique map `A ⊢ ⊤` being a monomorphism, where `⊤` is defined in `Grammar.Top.Base`.
- The map `Δ : A ⊢ A & A` being an isomorphism, where `&` is a binary product defined in `Grammar.Product.Binary.AsPrimitive`.

### Lemma 4.3

> If `B` is unambiguous and `A` is a retract of `B`, then `A` is unambiguous.

Given in `Grammar.Properties.Base` as `isUnambiguousRetract`.

### Lemma 4.4

>If a binary disjunction `A ⊕ B` is unambiguous then `A` and `B` are each unambiguous

For binary sums implemented via Agda's sum types, given in `Grammar.Sum.Binary.AsPrimitive.Properties` as `summand-L-is-unambig` and `summand-R-is-unambig`.

For binary sums implemented as indexed sums over `Bool`, given in `Grammar.Sum.Binary.AsIndexed.Properties` as `unambig-summands`.

### Definition 4.5

> Linear types `A` and `B` are _disjoint_ if there is a function `↑ (A & B ⊸ 0)`

Given in `Grammar.Properties.Base`.

### Definition 4.6

> A parser for a linear type `A` is the choice of a type `B` disjoint from `A` and a function `↑ (string ⊸ A ⊕ B)`

Given in `Parser.Base`.

### Lemma 4.7

> If `⊕[ x ∈ X ] A x` is unambiguous, then for `x ≢ x'`, `A x` and `A x'` are disjoint. In particular, if the binary product `A ⊕ B` is unambiguous, then `A` and `B` are disjoint.

Given for all indexed sums as `hasDisjointSummands⊕ᴰ` in `Grammar.Sum.Unambiguous`. This lemma is a consequence of the disjoint constructors axioms, which is encoded in the same file as `equalizer→⊥`.

For the binary sums implemented in `Grammar.Sum.Binary.AsPrimitive`, we prove this lemma in `Grammar.Sum.Binary.AsPrimitive.Properties` under the name `unambig-⊕-is-disjoint`.

### Lemma 4.8

> If `A` is weakly equivalent to `B`, then any parser for `A` can be extended to a parser for `B`.

Defined as `≈Parser` in `Parser.Base`.

### Theorem 4.9

> Given a DFA `D`, we construct a function `parse D s` that is a parser for `Trace D s true`

DFAs are defined in `Automata.DFA.Base`. The type `DFA` is implemented using a more general construction `DeterministicAutomaton` from `Automata.Deterministic`.

`DeterministicAutomaton` encodes a deterministic labelled transition system over a type of states `Q : Type ℓ`. A `DFA` is then a `DeterministicAutomaton` where the type of states is a finite set.

A parser for a `DeterministicAutomaton` is given in `Automata.Deterministic` as `AccTraceParser`. Because `DFA` is just a special case of this more general automaton, `AccTraceParser` is also a parser for `DFA`s.

### Construction 4.10 (Determinization)

> Given an NFA `N`, we construct a DFA `D` such that `Parse N` is weakly equivalent to `Parse D`.

NFAs are defined in `Automata.NFA.Base`. The determinization construction is given in `Determinization.WeakEquivalence` as `NFA≈DFA`.

There are a couple of non-linear analyses we perform over an NFA `N : NFA` to enable this construction:

1. Given several traces through `N`, the determinization construction needs to deterministically choose one. A priori, the states of `N`, the type of labelled transitions in `N`, and the type of `ε`-transitions in `N` are each finite sets. To enable the choice function for traces through `N`, we require each of these types are not just finite sets, but that they are further __finitely ordered__. By making each of these types ordered, we then have a well-defined way to choose the __smallest__ trace when determinizing.
  - The definitions of `isFinSet` (a finite set) and `isFinOrd` (a finite order) may be found in the Cubical standard library under `Cubical.Data.FinSet`.

2. When building the powerset DFA, we define a `DFA` whose states are `ε`-closed subsets of states in `N`. To begin to reason about these `ε`-closed subsets, we need to decide if there is a path in `N` between any two states solely through `ε`-transitions. To make that decision, in `Cubical.Data.Quiver.Reachability` we prove that in any finite `Quiver` we can decide whether any two nodes are connected. To build the `ε`-closed subsets for the DFA, we then instantiate our `Quiver.Reachability` module with a `Quiver` whose nodes are the states of `N` and whose edges are the `ε`-transitions of `N`.

### Construction 4.11 (Thompson's Construction)

> For a regular expression `r`, we construct an NFA `N` such that `r` is strongly equivalent to `Parse N`.

In `Grammar.RegularExpression.Base`, we define a non-linear type of regular expressions and its interpretation as grammars (`RegularExpression` and `RegularExpression→Grammar`, respectively).

Then in the module `Thompson.Construction`, we have a submodule for each regular expression constructor. Each of these submodules builds the corresponding `NFA` and proves that the `NFA` is strongly equivalent to that case of regular expression. For instance, `Thompson.Construction.Literal` takes in a character `c : ⟨ Alphabet ⟩`, constructs `literalNFA c : NFA ℓ-zero`, and then proves that the parses of `literalNFA c` and `＂ c ＂` are strongly equivalent as grammars.

`Thompson.Equivalence` gathers up all of the equivalences from `Thompson.Construction` and recursively proves that every regular expression is strongly equivalent to the parses of its corresponding `NFA`.

### Corollary 4.12

> We may build a parser for every regular expression `r`

We combine Thompson's construction and doterminization to build a parser for an arbitrary regular rexpression in `Examples.RegexParser`.

### Theorem 4.13

> `Dyck` and `Parse M` are strongly equivalent, so we may build a parser for `Dyck`.

`Examples.Dyck` contains `Dyck`, the grammar of balanced parentheses. In this file we instantiate the module `Automata.Deterministic` to build the machine `M` depicted in Figure 12.

The term `Dyck≅Trace` shows that the accepting traces of this automaton are strongly equivalent to `Dyck`. Finally, `DyckParser` is the `Parser` for `Dyck` that arises from porting the parser for the accepting traces of the automaton over the equivalence between `Dyck` and the type of accepting traces.

### Theorem 4.14

> We construct a parser for `Exp` by showing that it is weakly equivalent to the accepting traces from the opening state with its stack set to `0`.

In `Examples.BinOp`, we define a grammar of arithmetic expressions over a binary operation `+`.

The module `LL⟨1⟩` found in this file defines the grammars `EXP` and `ATOM`. The module `Automaton` in this file defines the lookahead automaton given in Figure 13.

`Automaton.TraceParser` defines a parser for the accepting traces beginning at any state in the lookahead automaton.

The module `Soundness` in this file builds a term `buildExp` from the accepting traces out of the initial state of the automaton to `EXP`. The module `Completeness` builds a term `mkTrace` from `EXP` to the type of accepting traces from the initial state.

We then combine the terms `buildExp` and `mkTrace` in `AccTrace≈EXP` to show that `EXP` and `Trace true (0 , Opening)` are weakly equivalent. `EXPParser` is then the parser for `EXP` that arises from combining `AccTrace≈EXP` and `Automaton.TraceParser`.

### Construction 4.15

> For any Turing machine `T`, we construct a grammar that accepts the same language as `T`.

In `Grammar.Reify.Base`, we define the `Reify` grammar

``` agda
module _ (P : String → Type ℓA) where
  Reify : Grammar ℓA
  Reify = ⊕[ w ∈ String ] ⊕[ x ∈ P w ] ⌈ w ⌉
```

`Reify` allows the user to treat the non-linear type-valued function `P` as if it were a proper linear type.

In `Automata.Turing.OneSided.Base`, we define a non-linear type of Turing machine specifications `TuringMachine`. Then for a fixed Turing machine `TM : TuringMachine`, we define a type of traces through that machine `TuringTrace`.

We then define `Accepting : String → Type ℓ-zero` as the non-linear type of proofs that a given string is accepted by `TM` when ran from the initial state. `Reify` enables the non-linear function `Accepting` to be treated as a grammar.

``` agda
Turing : Grammar ℓ-zero
Turing = Reify Accepting
```

### Axiom 3.1

> Additive conjunction distributes over additive disjunction

Given in `Grammar.Distributivity`.

### Corollary 3.2

> The constructors of a binary sum, `inl` and `inr` are injective

Given in `Grammar.Sum.Binary.AsPrimitive.Properties` as `isMono-⊕-inl` and `isMono-⊕-inr`.

### Axiom 3.3

> The constructors of sums are disjoint.

Given as `equalizer→⊥` in `Grammar.Sum.Unambiguous`.

### Axiom 3.4

> We add a function `read : ↑ (⊤ ⊸ string)`.

Given as `read` in `Grammar.String.Terminal`.

> `⊤` is strong equivalent to `string`.

Given as `string≅⊤` in `Grammar.String.Terminal`.

## Project Layout
The codebase is in the `src` directory, and it is split into the following submodules,
- `String` - contains the definition as the list type over some fixed alphabet, and some associated utilities. `String := List ⟨ Alphabet ⟩`, where `Alphabet : hSet ℓ-zero`
- `Grammar` - defining the primitive linear types in Dependent Lambek Calculus. Linear types are encoded as functions from strings to types, written as `Grammar ℓA = String → Type ℓA`.
- `Term` - defining parse transformers between grammars. A parse transformer between `A` and `B` is written as the type `A ⊢ B` (or `Term A B`).
- `Parser` - the definition of a parser as described in definition 4.4.
- `Automata` - defining the following automata formalisms as grammars: DFAs, NFAs, deterministic (but not necessarily finite) automata, and Turing machines.
- `Examples` - containing intrinsically verified parsers for the Dyck grammar, an arithmetic expression grammar, and arbitrary regular expressions. Additionally has the examples from the figures in Section 2 encoded.
- `Thompson` - a verification of Thompson's construction: from a regular expression `r` construct an NFA and prove that it is strongly equivalent to `r`.
- `Determinization` - a verification of the powerset construction for determinization. Given an NFA `N`, construct a DFA that is weakly equivalent to it.
- `Cubical` - general purpose utilities that supplement the `Cubical` standard library in ways not specific to grammars.

## Dependent Lambek Calculus in Agda
Dependent Lambek Calculus (`Lambekᴰ`) is a domain-specific dependent type theory for verified parsing and formal grammar theory. We use linear types as a syntax for formal grammars, and parsers can be written as linear terms. The linear typing restriction provides a form of intrinsic verification that a parser yields only valid parse trees for the input string.

We build an implementation of Dependent Lambek Calculus by as a *shallow embedding* in Cubical Agda. That is, we define the constructs used in the denotational semantics and program directly using the denotations. The syntax is then interpreted via the following encodings:

### Non-linear Types
The non-linear types of `Lambekᴰ` are embedded by reusing Agda's type system. The universe of non-linear types `U` is interpreted in this implementation at `Type ℓ` (at some level `ℓ`).

Because we reuse the host language to encode the non-linear types, we give no embedded syntax for the non-linear fragment of `Lambekᴰ`. That is, the non-linear `Lambekᴰ` types `X Y : U` are interpreted as Agda types `X Y : Type ℓ`. The non-linear terms from `Γ , X ⊢ Y` from `Lambekᴰ` are interpreted by the type of dependent functions between `X` and `Y`. Non-linear variables are scoped by Agda, so the non-linear context `Γ` is implicitly managed by Agda.

In the denotational semantics of `Lambekᴰ`, `U` is interpreted in the category `Set`. Therefore, in this implementation it is more precise to interpret the non-linear types into `hSet ℓ`, Agda's type of homotopy sets. In Cubical Agda, a set `X : hSet ℓ` is a pair of an underlying type `⟨ X ⟩` and a proof `isSet ⟨ X ⟩` encoding that `⟨ X ⟩` is a set. Instead of parameterizing the constructs in our implementation by sets, we instead often write them more generally to only be parameterized by types. Then when programming in `Lambekᴰ` we provide the `isSet` proof as a side condition.

### Non-commutative Linear Types
The non-commutative linear types of `Lambekᴰ` are interpreted as functions from a type of strings into the universe of Agda's types. Precisely, we fix a set of characters `Alphabet : hSet ℓ-zero` and define `String` as `List ⟨ Alphabet ⟩`. Then in `Grammar.Base` we give the interpretation of linear types,
``` agda
Grammar : Type (ℓ-suc ℓA)
Grammar = String → Type ℓA
```

For a grammar `A : Grammar ℓA` and a string `w : String`, the type `A w : Type ℓA` encodes the parse trees of `w`  for the grammar `A`. An inhabitant `p : A w` then is a single parse tree.

The denotational semantics of our non-commutative linear types are as functions from strings to *sets*, but the above definitions at first appear too general because they map into `Type ℓA` instead of `hSet ℓA`. Just as with the non-linear types, we separate the linear type from the proof that it is set valued. In `Grammar.Hlevels.Base` we define `isSetGrammar` which is our linear analog to Agda's `isSet`. We further prove that each typing connective respects being set valued, then when writing a parser the `isSetGrammar` proofs can be provided as side conditions.

#### Grammar Connectives
The typing connectives of `Lambekᴰ` are given in the `Grammar` module. Here we include a summary of a selection of the modules.

##### Concatenation
For instance, the concatenation of grammars is given in `Grammar.LinearProduct.Base`:

``` agda
_⊗_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A ⊗ B) w = Σ[ s ∈ Splitting w ] A (s .fst .fst) × B (s .fst .snd)
```

where `Splitting w` is the data of two substrings `w₁ w₂ : String`, such that `w₁ ++ w₂ ≡ w`. In the above code, `w₁` and `w₂` are written as `s .fst .fst` and `s .fst .snd`, respectively. That is, a string is parsed by the concatenation of `A` and `B` if that string may be split into two substrings such that `A` parses the left substring and `B` parses the right substring.

##### Linear Unit
Similarly, the nullary concatenation, written as `I` in the paper, is given in `Grammar.Epsilon.Base`:

``` agda
ε : Grammar ℓ-zero
ε w = w ≡ []
```

A string matches `ε` if and only if it is the empty string.

##### Empty Grammar
The empty grammar `0 : L`, which is given as a nullary sum, is implemented in `Grammar.Bottom.Base` using Agda's empty type,

``` agda
⊥ : Grammar ℓ-zero
⊥ _ = Empty.⊥
```

We use `⊥` to avoid a name clash with the number `0`.

##### Products and Sums
In `Grammar.Product.Base` we define indexed conjunction as a `Π`-type.

``` agda
&ᴰ : {X : Type ℓX} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
&ᴰ {X = X} f w = ∀ (x : X) → f x w
```

Given `A : X → Grammar ℓA`, the grammar `&ᴰ A` may sometimes be written as `&[ x ∈ X ] A x`.

We can define binary products as an indexed product over `Bool`, which we give in `Grammar.Product.Binary.AsIndexed`.

We may instead define a primitive where the binary product is implemented semantically as a pair, given in `Grammar.Product.Binary.AsPrimitive`.

``` agda
_&_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A & B) w = A w × B w
```

Further, in `Grammar.Product.Binary.AsPrimitive.Properties`, we prove that these two different binary product types are equivalent.

Similarly, we define indexed sums in `Grammar.Sum.Base` and give two equivalent implementations of binary sums in `Grammar.Sum.Binary.AsIndexed` and `Grammar.Sum.Binary.AsPrimitive`.

### Linear Terms

In `Lambekᴰ`, a derivation `Γ ; A ⊢ B ` denotes a parse transformer that translates parses of grammar `A` into parses of grammar `B`. These parse transformers are encoded in this `Term.Base` via the type,

``` agda
module _ (A : Grammar ℓA) (B : Grammar ℓB) where
  Term : Type (ℓ-max ℓA ℓB)
  Term : ∀ (w : String) → A w → B w
```

That is, a parse transformer from `A` to `B` is a function that that maps parses of `A` to parses of `B` for each input string `w`.

We often write `A ⊢ B` as a synonym for `Term A B`.

#### Contexts
Because the non-linear types are implemented using Agda's `Type`, the encoding of a `Lambekᴰ` derivation `Γ ; A ⊢ B` does not need to explicitly be reference `Γ`. The non-linear variables are scoped by Agda.

The linear contexts in the implementation are unary, so the `Lambekᴰ` derivations of the form `A , B ⊢ C` are represented in the code as terms `A ⊗ B ⊢ C`. Similarly, `Lambekᴰ` terms in the empty context `∙ ⊢ A` are represented in the code as terms `ε ⊢ A`.

#### `A ⊢ B` vs. `↑ (A ⊸ B)`
In the paper syntax, we write `↑ (A ⊸ B)` to describe the parse transformers from `A` to `B`.

For a grammar `C`, `↑ C` denotes the parses of `C` in the empty context and we define this encoding in `Term.Nullary`. By leveraging the adjunction between `⊗` and `⊸`, and using the fact that `ε` is the unit for `⊗`, it is true that `↑ (A ⊸ B)` and `A ⊢ B` are equivalent types. This equivalence is proven in `Grammar.LinearFunction.Base` with `Term≅Element`. However, in this implementation we almost exclusively use `A ⊢ B` to encode parser transformers instead of `↑ (A ⊸ B)`.

Because the two types are equivalent, the choice of representation does not affect any of the semantic claims. We prefer to use `A ⊢ B` in the formalization because it makes associativity and unit laws for composition hold definitionally in Agda.

#### Some Example Linear Terms
The linear terms in our implementation are written in a combinatory style, rather than in exactly the same syntax presented in the paper. The parse transformers in the implementation must then be built up from base combinators in a point-free style.

For instance, in Figure 1 of the paper we provide the linear term in `Lambekᴰ`:

``` agda
f : ↑ (＂ a ＂ ⊗ ＂ b ＂ ⊸ (＂ a ＂ ⊗ ＂ b ＂) ⊕ ＂ c ＂)
f (a , b) = inl (a ⊗ b)
```

`f` matches on its input which is a tensor and introduces two parse trees, `a : ＂ a ＂` and `b : ＂ b ＂`. Then `f` recombines these parse trees with a tensor and calls `inl`.

Our implementation captures the same parse transformer, except we do not have the ability to introduce named variables in this manner. Instead, the same parse transformer is implemented in `Examples.Section2.Figure1` using the `inl` combinator from `Grammar.Sum.Binary.AsPrimitive`.

``` agda
f : ＂ a ＂ ⊗ ＂ b ＂ ⊢ ＂ a ＂ ⊗ ＂ b ＂ ⊕ ＂ c ＂
f = inl
```

Similarly, in Figure 3 we give the `Lambekᴰ` term

``` agda
g : ↑ (＂ a ＂ ⊗ ＂ b ＂ ⊸ ((＂ a ＂ *)  ⊗ ＂ b ＂) ⊕ ＂ c ＂)
g (a , b) = inl (cons a nil ⊗ b)
```

This same parse transformer is given via combinators in `Examples.Section2.Figure3`

``` agda
g : ＂ a ＂ ⊗ ＂ b ＂ ⊢ (＂ a ＂ *) ⊗ ＂ b ＂ ⊕ ＂ c ＂
g = inl ∘g (CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id
```

Note, in this implementation the contexts `A , ·`, `· , A`, and `A` are encoded differently. On paper, the empty context is definitionally a unit for context extension, but in the term `g` above we must manually insert an empty piece of the context through the combinator `⊗-unit-r⁻ : ∀ {A : Grammar ℓA} → A ⊢ A ⊗ ε`.

## Caveats

### Combinators
The parse transformers built in this implementation must be written in a combinatory style without mention to any named linear variables. This is the biggest departure of this codebase from the syntax presented in the paper.

The two systems have equivalent semantics, so this difference does not affect any of the claims supported by this artifact.

To bridge the gap between the paper syntax and this codebase, in the future we may write an ordered, linear typechecker that elaborates the full syntax into a combinatory core language.


### Opacity
Many of the definitions in this repository are marked as `opaque`. [Opacity](https://agda.readthedocs.io/en/v2.7.0.1/language/opaque-definitions.html) is a feature in Agda that allow selective unfolding of definitions.

When normalizing, a term defined in an `opaque` block will not reduce unless it is explicitly marked with an `unfolding`. Opacity is also infective in that any definition that wishes to unfold an `opaque` definition must itself be marked as `opaque`.

We use opacity for several reasons:
- Reducing typechecking time by limiting unnecessary normalizations.
- Putting up an explicit barrier between the embedded language and the host language. By marking our language primitives as `opaque` we gain finer grained control of their unfoldings. In particular, we can ensure that certain equalities occur in the embedded equational theory of `Lambekᴰ` rather than by happenstance in Agda.

The most faithful encoding of `Lambekᴰ` would only break these abstraction boundaries when axiomatizing a language primitive. Usage of any language constructs, and proofs about any language constructs would then occur without any explicit `unfolding`. This strategy would guarantee that any proofs of equality between linear terms follows only from equational reasoning in `Lambekᴰ`. That is, there would be no possibility to "accidentally get an equality correct" by leveraging external reasoning available in Agda that isn't available in `Lambekᴰ`.

We have kept this attitude in mind throughout the development and tried to unfolding minimally. However, by unfolding we also can enable Agda to solve for `β`-equalities within `Lambekᴰ` that would otherwise be long chains of manually invoked lemmas.

#### An example with `⊗-intro`
For example, consider the following two terms,

``` agda
module _ (e : A ⊢ B) (f : B ⊢ C) (g : D ⊢ E) (h : E ⊢ F) where
  ϕ ψ : A ⊗ B ⊢ C ⊗ F
  ϕ = (f ∘g e) ,⊗ (h ∘g g)
  ψ = (f ,⊗ h) ∘g (e ,⊗ g)
```

A priori, `ϕ` and `ψ` are not definitionally equal. We may derive their equality, but that involves manual reasoning every time that we compose maps in parallel. Instead, if we unfold the definition of `⊗-intro`, then `ϕ` and `ψ` become definitionally equal. So in the strictest sense, unfolding `⊗-intro` could have accidentally invoked external reasoning that doesn't hold in `Lambekᴰ`. In practice, we are careful to only unfold so that we may use Agda's definitional equality as a rudimentary solver for `β`-equalities that hold in `Lambekᴰ`.

We apply this same principle throughout all of our code. Any instance of unfolding is either a deliberate breaking of abstraction boundaries to build the language, or it is to have Agda solver for equalities that are derivable within `Lambekᴰ` anyway.

Here are the other terms that we unfold to solve for `β`-equalities:
- `⊕-elim` from `Grammar.Sum.Binary.AsPrimitive` so that we can leverage the definitional equalities that hold over Agda's `Sum` type.
- `π₁`/`π₂` from `Grammar.Product.Binary.AsPrimitive` so that we can leverage the definitional equalities that hold over Agda's `×` type.
- `⊕ᴰ-distL`/`⊕ᴰ-distR` from `Grammar.Sum.Properties` and their counterparts from `Grammar.Sum.Binary.AsPrimitive`. Unfolding these allows distributivity of sums over `⊗` to reduce.
- A combination of `⊗-intro`, `⊗-unit-l`/`⊗-unit-r`, `⊗-unit-l⁻`/`⊗-unit-r⁻` and `⊗-assoc` to use these equalities from `Grammar.LinearProduct.Base`:
  - `⊗-assoc⁻4⊗-intro`
  - `id,⊗id≡id`
  - `⊗-unit-r⁻⊗-intro`
  - `⊗-unit-l⁻⊗-intro`
  - `⊗-assoc⁻⊗-intro`
- `eq-intro` from `Grammar.Equalizer.Base` to expose that it is the identity on parse trees while additionally tagging a parse with a proof of equality.

### Unsafe Pragmas
#### Termination Checking
We make use of the `TERMINATING` pragma in the following locations:

- `Grammar.Inductive.HLevels` in the definitions of `encode` and `isRetract`.
- `Grammar.Inductive.Indexed` in the definitions of `recHomo` and `μ-η'`.
- `Examples.Benchmark.Dyck` to generate strings. The string generation code is untrusted and only used to create tests.

In `Grammar.Inductive.Functor`, we define a type of strictly positive functors that act on grammars. We then define the least fixed point `μ` of these functors in `Grammar.Inductive.Indexed` in a manner that does not satisfy Agda's termination checker, so we use the `TERMINATING` pragma to suppress the termination checker.

In `Grammar.Inductive.HLevels` we prove that `μ` is a retract of an `IW` tree (or indexed container), which are well-founded. The use of `TERMINATING` in `Grammar.Inductive.HLevels` is necessary to build this retraction. Because `IW` trees are well-founded, this retraction establishes that `μ` are also well-founded and that the use of these `TERMINATING` pragmas is safe.

#### Positivity Checking
Additionally we use a `NO_POSITIVITY_CHECK` pragma in:
- `Grammar.Inductive.Indexed`

Our use of opacity in the connective `⊗` blocks the positivity checker for the definition of `μ` in `Grammar.Inductive.Indexed`. If `⊗` were not opaque, [then this definition would pass the positivity checker](https://github.com/agda/agda/issues/6970).

In any case, this `NO_POSITIVITY_CHECK` pragma is also safe following the proof in `Grammar.Inductive.HLevels` that `μ` is well-founded.

### `-WnoUnsupportedIndexedMatch`

We frequently suppress a warning introduced when pattern matching on [indexed inductive types](https://agda.readthedocs.io/en/latest/language/cubical.html#indexed-inductive-types) in Cubical Agda. Suppressing this warning is harmless, and suppression is even recommended in the linked documentation for most end users of Cubical.

### Runtime and IO
One drawback of embedding the language in Agda is that the typechecker is now acting as a parser, which is rather slow.

Additionally, we have not interfaced with any of Agda's `IO` modules. Instead, all of our experiments have either mocked the parsing input as its own Agda file that contains a string literal of the data to be parsed or have a function that generates the input.

For the `Dyck` example, we ran some simple benchmarks in `Examples.Benchmark.Dyck`. The verified parser for `Dyck` takes `1m3s` to parse an input string that is `196544` characters long. This runtime also includes the time to generate the input string, which is estimated to be around `20s` on its own.
