module SemanticAction.CSV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Empty renaming (⊥ to EmptyType)
open import Cubical.Data.List as List
import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base renaming (Dec to NLDec; decRec to nlDecRec)

open import String.ASCII
open import String.Unicode
open import Grammar ASCII
open import Grammar.Inductive.Indexed ASCII
open import Term ASCII
open import SemanticAction.Base ASCII
open import SemanticAction.Monadic ASCII
open import ParserCombinator.Base ASCII as Parser hiding (pure; char)

module Concrete where
  parseQuote : WeakParser (literal DOUBLEQUOTE)
  parseQuote = Parser.char DiscreteASCIIChar DOUBLEQUOTE

  isQuotedChar : ⟨ ASCII ⟩ → Type ℓ-zero
  isQuotedChar c = c ≡ DOUBLEQUOTE → EmptyType

  QuotedChar : Grammar ℓ-zero
  QuotedChar = ⊕[ c ∈ ⟨ ASCII ⟩ ] ⊕[ _ ∈ isQuotedChar c ] literal c

  parseQuotedChar : WeakParser QuotedChar
  parseQuotedChar = satisfy λ c →
    nlDecRec (λ p → no λ ¬p → ¬p p) yes (DiscreteASCIIChar c DOUBLEQUOTE)

  QuotedLit : Grammar ℓ-zero
  QuotedLit = QuotedChar ⊕ (literal DOUBLEQUOTE ⊗ literal DOUBLEQUOTE)

  parseQuotedLit : WeakParser QuotedLit
  parseQuotedLit = parseQuotedChar <|> (parseQuote <⊗> parseQuote)

  QuotedField : Grammar ℓ-zero
  QuotedField = KL* QuotedLit

  parseQuotedField : WeakParser QuotedField
  parseQuotedField = many parseQuotedLit

  isUnquotedChar : ⟨ ASCII ⟩ → Type ℓ-zero
  isUnquotedChar c =
    (c ≡ COMMA → EmptyType)
    × (c ≡ DOUBLEQUOTE → EmptyType)
    × (c ≡ NEWLINE → EmptyType)

  UnquotedLit : Grammar ℓ-zero
  UnquotedLit = ⊕[ c ∈ ⟨ ASCII ⟩ ] ⊕[ _ ∈ isUnquotedChar c ] literal c

  parseUnquotedLit : WeakParser UnquotedLit
  parseUnquotedLit = satisfy λ c →
    nlDecRec (λ p → no λ ¬p → ¬p .fst p)
      (λ comma → nlDecRec (λ p → no λ ¬p → ¬p .snd .fst p)
        (λ dblquote → nlDecRec (λ p → no λ ¬p → ¬p .snd .snd p)
          (λ newline → yes (comma , dblquote , newline))
          (DiscreteASCIIChar c NEWLINE))
        (DiscreteASCIIChar c DOUBLEQUOTE))
      (DiscreteASCIIChar c COMMA)

  UnquotedField : Grammar ℓ-zero
  UnquotedField = KL* UnquotedLit

  parseUnquotedField : WeakParser UnquotedField
  parseUnquotedField = many parseUnquotedLit

  Field : Grammar ℓ-zero
  Field = UnquotedField ⊕ (literal DOUBLEQUOTE ⊗ QuotedField ⊗ literal DOUBLEQUOTE)

  parseField : WeakParser Field
  parseField =
    parseUnquotedField
    <|> parseQuote <⊗> parseQuotedField <⊗> parseQuote

  EOL : Grammar ℓ-zero
  EOL = literal NEWLINE

  parseEOL : WeakParser EOL
  parseEOL = Parser.char DiscreteASCIIChar NEWLINE

  NonemptyLine : Grammar ℓ-zero
  NonemptyLine = Field ⊗ KL* (literal COMMA ⊗ Field)

  parseNonemptyLine : WeakParser NonemptyLine
  parseNonemptyLine = parseField <⊗> many (Parser.char DiscreteASCIIChar COMMA <⊗> parseField)

  Line : Grammar ℓ-zero
  Line = (ε ⊕ NonemptyLine) ⊗ EOL

  parseLine : WeakParser Line
  parseLine = (Parser.pure ε-intro <|> parseNonemptyLine) <⊗> parseEOL

CST : Grammar ℓ-zero
CST = KL* Concrete.Line

concrete-parser : WeakParser CST
concrete-parser = many Concrete.parseLine

module Abstract where
  Field : Type ℓ-zero
  Field = List ASCIIChar

  Line : Type ℓ-zero
  Line = List Field

AST : Type ℓ-zero
AST = List Abstract.Line

module Concrete→Abstract where
  quotedLit : SemanticAction Concrete.QuotedLit String
  quotedLit = semact-⊕ semact-underlying (semact-pure [ DOUBLEQUOTE ])

  quotedField : SemanticAction Concrete.QuotedField Abstract.Field
  quotedField = semact-map (List.foldl _++_ []) (semact-* quotedLit)

  field' : SemanticAction Concrete.Field Abstract.Field
  field' = semact-⊕ semact-underlying (semact-surround quotedField)

  nonemptyLine : SemanticAction Concrete.NonemptyLine Abstract.Line
  nonemptyLine =
    semact-map (uncurry _∷_) (semact-concat field'
      (semact-* (semact-right field')))

  nonemptyLine' : SemanticAction (Concrete.Field ⊗ ((literal COMMA ⊗ Concrete.Field) *) ⊗ ε) Abstract.Line
  nonemptyLine' = do
    x ← field'
    xs ← semact-* (semact-right field')
    pure (x ∷ xs)

  line : SemanticAction Concrete.Line Abstract.Line
  line = semact-left (semact-⊕ (semact-pure []) nonemptyLine)

  ast : SemanticAction CST AST
  ast = semact-* line

parser : WeakParser (Δ AST)
parser = Parser.map (⊸-elim-ε Concrete→Abstract.ast) concrete-parser

module Test where
  open import Test ASCII

  open DecodeUnicode ASCII Unicode→ASCII

  s : String
  s = []

  p : Maybe.Maybe (literal DOUBLEQUOTE s)
  p = runWeakParser Concrete.parseQuote s

  q : Maybe.Maybe (ε s)
  q = runWeakParser {g = ε} (Parser.pure (ε-intro)) s

  csv1 : String
  csv1 = mkString "a,b,c\ne,f,g"

  csv1-cst : Maybe.Maybe (CST csv1)
  csv1-cst = runWeakParser concrete-parser csv1

  csv1-data : Maybe.Maybe AST
  csv1-data = runWeakParserΔ parser csv1

  opaque
    unfolding ⊗-unit-r' ⊗-assoc internalize ⌈w⌉→string runWeakParserΔ ⊕ᴰ-distR ⊗-unit-r ⊗-unit-l⁻ ⊤* ⊤ ε ⊗-intro internalize' ⊕-elim runWeakParser literal ⟜-intro ⊸-intro ⟜-app ⊸-app
    _ : p ≡ Maybe.nothing
    _ = refl

    εmt : ε []
    εmt = refl

    _ : q ≡ Maybe.just εmt
    _ = refl

    _ : csv1 ≡ a^ ∷ COMMA ∷ b^ ∷ COMMA ∷ c^ ∷ NEWLINE ∷ e^ ∷ COMMA ∷ f^ ∷ COMMA ∷ g^ ∷ []
    _ = refl

    _ : csv1-cst ≡ Maybe.just {!!}
    _ = {!refl!}
