import LambekD.Tactic.Base
import LambekD.Grammar.Tensor
import LambekD.Grammar.Sum
import LambekD.Grammar.Product
import LambekD.Grammar.FunctionR
import LambekD.Grammar.FunctionL
import LambekD.Grammar.Top
import LambekD.Grammar.Bottom
import LambekD.Grammar.Equivalence

/-!
# `@[grammar_simp]` lemma tagging

Tags the β/η laws, composition laws, and string lemmas for use with
`simp [grammar_simp]`.
-/

open LambekD

-- String / List lemmas for splitting proofs
attribute [grammar_simp] List.append_assoc List.nil_append List.append_nil

-- Composition laws (all hold by rfl)
attribute [grammar_simp] gComp_assoc gId_comp gComp_id

-- Tensor bifunctoriality
attribute [grammar_simp] gtensorIntro_comp gtensorIntro_id

-- Sum β/η
attribute [grammar_simp] gsum_βl gsum_βr gsum_η gsumElim_comp

-- Product β/η
attribute [grammar_simp] gprod_β₁ gprod_β₂ gprod_η gprodIntro_comp

-- Linear function η
attribute [grammar_simp] glimpR_η glimpL_η

-- Linear function intro composition
attribute [grammar_simp] glimpRIntro_comp glimpLIntro_comp
