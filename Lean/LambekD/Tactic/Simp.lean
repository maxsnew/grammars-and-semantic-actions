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
attribute [grammar_simp] tensorIntro_comp tensorIntro_id

-- Sum β/η
attribute [grammar_simp] sum_βl sum_βr sum_η sumElim_comp

-- Product β/η
attribute [grammar_simp] prod_β₁ prod_β₂ prod_η prodIntro_comp

-- Linear function η
attribute [grammar_simp] limpR_η limpL_η

-- Linear function intro composition
attribute [grammar_simp] limpRIntro_comp limpLIntro_comp
