import LambekD.Grammar
import LambekD.Monoidal

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

--------------------------------------------------------------------------------
-- Kleene Star
--------------------------------------------------------------------------------
inductive Star (A : SemGrammar.{u}) : SemGrammar where
 | nil : Star A []
 | cons : {w w' : SemString } → A w → Star A w' → Star A (w ++ w')

def StarFold {A B : SemGrammar.{u}} :
  Reduction Epsilon B →
  Reduction (Tensor A B) B →
  Reduction (Star A) B :=
  fun nilB consB w as =>
    match as with
    | Star.nil => nilB [] (EpsilonIntro (refl _))
    | Star.cons a as' => consB _ (TensorTy.mk (Splitting.mk _ _ (refl _)) a (StarFold nilB consB _ as'))
