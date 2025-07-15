import Lean
import LambekD.Semantics

open Lean Elab Meta PrettyPrinter Delaborator

universe u
section LambekDSyntax
variable [AlphabetStr]
open AlphabetStr

inductive Const
    | eps : Const
    | top : Const
    | bot : Const

inductive Lit
  | lit : Alphabet → Lit

inductive Ty
    | const : Const → Ty
    | lit : Lit → Ty
    | star : Ty → Ty
    | concat : Ty → Ty → Ty
    | disj : Ty → Ty → Ty
    -- | lfun : Ty → Ty → Ty
    -- | rfun : Ty → Ty → Ty

declare_syntax_cat const
syntax "I" : const
syntax "⊤" : const
syntax "⊥" : const

declare_syntax_cat literal
syntax "lit" "(" str ")" : literal

def elabConst : Syntax → MetaM Expr
  | `(const| I) => mkAppM ``Const.eps #[]
  | `(const| ⊤) => mkAppM ``Const.top #[]
  | `(const| ⊥) => mkAppM ``Const.bot #[]
  | _ => throwError "Unsupported type syntax"

def elabLit : Syntax → MetaM Expr
  | `(literal| lit($c:str)) => do
    -- Get the string value from the syntax
    let s := c.getString
    -- Use readLit to convert the string to Alphabet
    let a ← mkAppM ``AlphabetStr.readLit #[mkStrLit s]
    -- Wrap in Lit.lit
    mkAppM ``Lit.lit #[a]
  | _ => throwError "Unsupported type syntax"

declare_syntax_cat ty
syntax const : ty
syntax literal : ty
syntax:85 ty "*" : ty
syntax:5 ty "⊸" ty : ty
syntax:5 ty "⟜" ty : ty
syntax:50 ty "⊕" ty : ty
syntax:80 ty "⊗" ty : ty
syntax:90 "(" ty ")" : ty

partial def elabTy : Syntax → MetaM Expr
  | `(ty| $l:literal) => do
    let litExpr ← elabLit l
    mkAppM ``Ty.lit #[litExpr]
  | `(ty| $c:const) => do
    let constExpr ← elabConst c
    mkAppM ``Ty.const #[constExpr]
  | `(ty| $t:ty *) => do
    let t' ← elabTy t
    mkAppM ``Ty.star #[t']
  | `(ty| $t1:ty ⊗ $t2:ty) => do
    let t1' ← elabTy t1
    let t2' ← elabTy t2
    mkAppM ``Ty.concat #[t1', t2']
  | `(ty| $t1:ty ⊕ $t2:ty) => do
    let t1' ← elabTy t1
    let t2' ← elabTy t2
    mkAppM ``Ty.disj #[t1', t2']
  | `(ty| ($t:ty)) => elabTy t
  | _ => throwError "Unsupported type syntax"

elab "ty!" t:ty : term => elabTy t

def SemTy : Ty → SemGrammar Alphabet :=
  fun t =>
  match t with
  | (Ty.const Const.eps) => Epsilon Alphabet
  | (Ty.const Const.top) => Terminal Alphabet
  | (Ty.const Const.bot) => Initial Alphabet
  | (Ty.lit (Lit.lit c)) => SemLiteral Alphabet c
  | (Ty.star A) => Star Alphabet (SemTy A)
  | (Ty.concat A B) => Tensor Alphabet (SemTy A) (SemTy B)
  | (Ty.disj A B) => Disjunction Alphabet (X := Bool)
                       (fun b => match b with
                        | true => SemTy A
                        | false => SemTy B)
  -- | (Ty.lfun x y) => sorry
  -- | (Ty.rfun x y) => sorry
  -- | _ => sorry

end LambekDSyntax

instance : AlphabetStr where
  Alphabet := String
  readLit x := x
  instInahbited := inferInstance
  instDecEq := inferInstance


elab "semTy!" t:ty : term => do
  let ty ← elabTy t
  mkAppM ``SemTy #[ty]
#reduce semTy! I
#reduce semTy! lit("a") ⊗ lit("b")
