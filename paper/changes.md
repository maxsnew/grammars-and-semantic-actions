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
We expand our discussion of the non-linear theory in Section 3.1. We clarify the
extensional equality type used, and we remove any assumption that the non-linear
theory has function extensionality because we don't use it in any
constructions. Instead we keep a brief discussion of function extensionality in Section
5.3 to highlight the convenience of function extensionality when working in the
shallow embedding, rather than a theoretical dependence on it.

## Comparisons with Related Work

### Luo's Lambek Calculus with Dependent Types
In Section 6.1, we correct our citation (Luo 2018) to reference both of his systems.

### Vákár's Categorical Semantics 
In Section 6.1, we add a paragraph discussing dependent linear types. We
contrast the way that different works, including (Vákár 2015), have encoded the `!` modality in a
dependent linear setting. Further, we discuss Vákár's general categorical
semantics and mention that a similar approach would likely apply when describing
a general categorical model of our system.

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



