# Changes Made in Revisions

Aside from minor typo fixes and changes in phrasing, these are the changes to
the paper.

## Including Full Typing Rules of Both Universes
The revised paper now contains a complete description of the language, including
both the non-linear and linear fragments.

We now provide context well-formedness rules in Figure 6; include the non-linear
rules in Figures 7, 18, and 19; include the linear rules in Figures
8, 9, and 20; and, include substitution rules in Figures 21 and 22.

## Discussion of Axioms
Each axiom is now distinguished with an axiom environment. 
In particular, around Corollary 3.2 and each of Axioms
3.1, 3.3, and 3.4, we now have brief discussions of their importance and/or
references to where each is used.

We also refer back to each
axiom when it is used. That is, Lemma 4.4 is
updated to highlight its dependence on Corollary 3.2, Lemma 4.7 is updated to
reference Axiom 3.3, and Theorem 4.14 is updated to reference Axiom 3.1.

In addition to the equational axioms, in the appendix we show that the
denotational semantics validates Axioms 3.1, 3.3, and 3.4. This is mentioned at
the end of Section 5.2.

## Discussion of Extensionality

We expand our discussion of the non-linear theory in Section 3.1. We
clarify that the equality type we use is an extensional equality type
with an equality reflection rule, and why this does not cause any
issues with our implementation method. We mention that equality
reflection implies function extensionality and so porting our
development to an intensional type theory may require a setoid construction.

We also have a brief discussion of function extensionality in Section
5.3, explaining why uniqueness of identity proofs holds for the
shallowly embedded types and note the convenience of function
extensionality in verifying the equations of the shallow embedding.

## Comparisons with Related Work

### Luo's Lambek Calculus with Dependent Types
In Section 6.1, we correct our citation (Luo 2018) to reference both of his systems.

### Vákár's Categorical Semantics 
In Section 6.1, we add a paragraph discussing prior work on dependent linear
 types, including (Vákár 2015) and its categorical semantics.
 

### Frisch and Cardelli's Greedy Parser
We split our discussion of (Frisch and Cardelli 2004) into two parts. The first,
in Section 6.1,
is a discussion of their type system for regular expressions, which is similar
to our discussion in the original submission.

The second is in 6.2 in an added paragraph on verified parser generators. We
discuss our intention to verify additional parsing algorithms with our theory,
including Frisch
and Cardelli's greedy algorithm. We mention that it is not obvious if this
greediness property could be verified easily.

## Additional Details on Implementation
In Section 5.3 we express the program from Figure 4 in our combinator style and
give a brief discussion the strengths and drawbacks of our current
implementation.

We more precisely describe the mapping from our universes into Cubical Agda.

We also give links to the Agda implementation. These are currently redacted for
double-blind reviewing, but we will later fill them in appropriately. 



