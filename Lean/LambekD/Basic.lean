import Lean

open Lean Elab Meta

section
variable {Alphabet : Type}
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]
include Alphabet

inductive Const
    | eps : Const
    | top : Const
    | bot : Const
    | lit : Alphabet → Const

inductive Binop
    | disj : Binop
    | concat : Binop

inductive Unaryop
    | star : Unaryop

inductive Ty
    | const : Const → Ty
    | un : Unaryop → Ty → Ty
    | bin : Binop → Ty → Ty → Ty

declare_syntax_cat const
syntax "I" : const
syntax "⊤" : const
syntax "⊥" : const
syntax str : const

declare_syntax_cat unaryop
syntax "*" : unaryop

declare_syntax_cat binop
syntax "⊕" : binop
syntax "⊗" : binop

def elabConst : Syntax → MetaM Expr
  | `(const| $c:str) => mkAppM ``Const.lit #[]
  | `(const| I) => mkAppM ``Const.eps #[]
  | `(const| ⊤) => mkAppM ``Const.top #[]
  | `(const| ⊥) => mkAppM ``Const.bot #[]
  | _ => throwError "Unsupported type syntax"

def elabBinop : Syntax → MetaM Expr
  | `(binop| ⊕) => return .const ``Binop.disj []
  | `(binop| ⊗) => return .const ``Binop.concat []
  | _ => throwError "Unsupported type syntax"

def elabUnaryop : Syntax → MetaM Expr
  | `(unaryop| *) => return .const ``Unaryop.star []
  | _ => throwError "Unsupported unary operator syntax"

declare_syntax_cat ty
syntax const : ty
syntax ty unaryop : ty
syntax ty binop ty : ty
syntax "(" ty ")" : ty

partial def elabTy : Syntax → MetaM Expr
  | `(ty| $c:const) => do
    let constExpr ← elabConst c
    mkAppM ``Ty.const #[constExpr]
  | `(ty| $t:ty $u:unaryop) => do
    let t' ← elabTy t
    let u' ← elabUnaryop u
    mkAppM ``Ty.un #[u', t']
  | `(ty| $t1:ty $b:binop $t2:ty) => do
    let t1' ← elabTy t1
    let t2' ← elabTy t2
    let b' ← elabBinop b
    mkAppM ``Ty.bin #[b', t1', t2']
  | `(ty| ($t:ty)) => elabTy t
  | _ => throwError "Unsupported type syntax"

elab "test_elabTy" t:ty : term => elabTy t
end

-- #reduce test_elabTy lit("hello")
-- #reduce test_elabTy (I ⊗ I)
-- #reduce test_elabTy ("hello" ⊗ I)
