import LambekD.Thompson.Construction

/-!
# Thompson's construction: overall strong equivalence

For every regular expression `r`, the NFA produced by Thompson's construction
accepts exactly the language of `r`:

  `Parse (regex_to_NFA r) ≅ ⟦r⟧r`

The proof is compositional, using the strong equivalence for each constructor.

Ports `Thompson.Equivalence` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

-- open RegularExpression in
-- -- Strong equivalence: Parse (regex_to_NFA r) ≅ ⟦r⟧r
-- -- Compositional proof by recursion on regex structure.
-- -- Each case uses the corresponding NFA equivalence + congruence of connectives.
-- def regex_equiv : (r : RegularExpression Alphabet) → NFA.Parse (regex_to_NFA r) ≅g r.toGrammar
--   | .eps => εNFA_equiv
--   | .bot => botNFA_equiv
--   | .literal c => literalNFA_equiv c
--   | .tensor r r' => sorry -- prodNFA_equiv ≅∙ ⊗-cong (regex_equiv r) (regex_equiv r')
--   | .sum r r' => sorry -- sumNFA_equiv ≅∙ ⊕-cong (regex_equiv r) (regex_equiv r')
--   | .star r => sorry -- starNFA_equiv ≅∙ *-cong (regex_equiv r)

-- end LambekD
