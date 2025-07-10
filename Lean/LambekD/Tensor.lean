import LambekD.Grammar

open Grammar

variable (Alphabet : Type)
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]
include Alphabet

def Tensor (A B : Grammar Alphabet) : Grammar Alphabet :=
  λ (w : SemString Alphabet) => (s : Splitting Alphabet w) × A (s.left) × B (s.right)

def Epsilon : Grammar Alphabet := λ (w : SemString Alphabet) => PLift (w = List.nil)

def TensorIn {A B C D : Grammar Alphabet} :
Reduction Alphabet A B → Reduction Alphabet C D →
  Reduction Alphabet (Tensor Alphabet A C) (Tensor Alphabet B D) :=
  fun f g _ ⟨s , ha , hc⟩ => ⟨s , f s.left ha, g s.right hc⟩

def EpsilonUnitR : {A : Grammar Alphabet} →
  Reduction Alphabet (Tensor Alphabet A (Epsilon Alphabet)) A := sorry

def EpsilonUnitRInv : {A : Grammar Alphabet} →
  Reduction Alphabet A (Tensor Alphabet A (Epsilon Alphabet)) := sorry

def EpsilonUnitL : {A : Grammar Alphabet} →
  Reduction Alphabet (Tensor Alphabet (Epsilon Alphabet) A) A := sorry

def EpsilonUnitLInv : {A : Grammar Alphabet} →
  Reduction Alphabet A (Tensor Alphabet (Epsilon Alphabet) A) := sorry
