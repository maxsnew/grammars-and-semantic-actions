import LambekD.Core.Defs

/-! # Distributivity axiom (Axiom 3.1) -/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

/-- **Axiom 3.1 (Distributivity)**: Indexed product distributes over indexed coproduct. -/
axiom distribIdxProdCoprod
    {X : Type} {Y : X → Type} {A : (x : X) → Y x → Grammar Alphabet} :
    (&[x ∈ X] ⊕[y ∈ Y x] A x y) ⊢ (⊕[f ∈ ((x : X) → Y x)] &[x ∈ X] A x (f x))

/-- Inverse direction of the distributivity axiom (derivable). -/
def distribIdxProdCoprodInv
    {X : Type} {Y : X → Type} {A : (x : X) → Y x → Grammar Alphabet} :
    (⊕[f ∈ ((x : X) → Y x)] &[x ∈ X] A x (f x)) ⊢ (&[x ∈ X] ⊕[y ∈ Y x] A x y) :=
  fun _ ⟨f, h⟩ x => ⟨f x, h x⟩

end LambekD
