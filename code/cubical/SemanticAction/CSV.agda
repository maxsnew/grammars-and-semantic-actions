module SemanticAction.CSV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Empty renaming (⊥ to EmptyType)
open import Cubical.Data.List as List
import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base renaming (Dec to NLDec; decRec to nlDecRec)

open import String.Unicode
open import Grammar Unicode
open import Grammar.Inductive.Indexed Unicode
open import Term Unicode
open import SemanticAction.Base Unicode
open import SemanticAction.Monadic Unicode
open import ParserCombinator.Base Unicode as Parser hiding (pure; char)

module Concrete where
  parseQuote : WeakParser (literal '"')
  parseQuote = Parser.char DiscreteUnicodeChar '"'

  isQuotedChar : ⟨ Unicode ⟩ → Type ℓ-zero
  isQuotedChar c = c ≡ '"' → EmptyType

  QuotedChar : Grammar ℓ-zero
  QuotedChar = ⊕[ c ∈ ⟨ Unicode ⟩ ] ⊕[ _ ∈ isQuotedChar c ] literal c

  parseQuotedChar : WeakParser QuotedChar
  parseQuotedChar = satisfy λ c →
    nlDecRec (λ p → no λ ¬p → ¬p p) yes (DiscreteUnicodeChar c '"')

  QuotedLit : Grammar ℓ-zero
  QuotedLit = QuotedChar ⊕ (literal '"' ⊗ literal '"')

  parseQuotedLit : WeakParser QuotedLit
  parseQuotedLit = parseQuotedChar <|> (parseQuote <⊗> parseQuote)

  QuotedField : Grammar ℓ-zero
  QuotedField = KL* QuotedLit

  parseQuotedField : WeakParser QuotedField
  parseQuotedField = many parseQuotedLit

  isUnquotedChar : ⟨ Unicode ⟩ → Type ℓ-zero
  isUnquotedChar c =
    (c ≡ ',' → EmptyType)
    × (c ≡ '"' → EmptyType)
    × (c ≡ '\n' → EmptyType)

  UnquotedLit : Grammar ℓ-zero
  UnquotedLit = ⊕[ c ∈ ⟨ Unicode ⟩ ] ⊕[ _ ∈ isUnquotedChar c ] literal c

  parseUnquotedLit : WeakParser UnquotedLit
  parseUnquotedLit = satisfy λ c →
    nlDecRec (λ p → no λ ¬p → ¬p .fst p)
      (λ comma → nlDecRec (λ p → no λ ¬p → ¬p .snd .fst p)
        (λ dblquote → nlDecRec (λ p → no λ ¬p → ¬p .snd .snd p)
          (λ newline → yes (comma , dblquote , newline))
          (DiscreteUnicodeChar c '\n'))
        (DiscreteUnicodeChar c '"'))
      (DiscreteUnicodeChar c ',')

  UnquotedField : Grammar ℓ-zero
  UnquotedField = KL* UnquotedLit

  parseUnquotedField : WeakParser UnquotedField
  parseUnquotedField = many parseUnquotedLit

  Field : Grammar ℓ-zero
  Field = UnquotedField ⊕ (literal '"' ⊗ QuotedField ⊗ literal '"')

  parseField : WeakParser Field
  parseField =
    parseUnquotedField
    <|> parseQuote <⊗> parseQuotedField <⊗> parseQuote

  EOL : Grammar ℓ-zero
  EOL = literal '\n'

  parseEOL : WeakParser EOL
  parseEOL = Parser.char DiscreteUnicodeChar '\n'

  NonemptyLine : Grammar ℓ-zero
  NonemptyLine = Field ⊗ KL* (literal ',' ⊗ Field)

  parseNonemptyLine : WeakParser NonemptyLine
  parseNonemptyLine = parseField <⊗> many (Parser.char DiscreteUnicodeChar ',' <⊗> parseField)

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
  Field = List UnicodeChar

  Line : Type ℓ-zero
  Line = List Field

AST : Type ℓ-zero
AST = List Abstract.Line

module Concrete→Abstract where
  quotedLit : SemanticAction Concrete.QuotedLit String
  quotedLit = semact-⊕ semact-underlying (semact-pure [ '"' ])

  quotedField : SemanticAction Concrete.QuotedField Abstract.Field
  quotedField = semact-map (List.foldl _++_ []) (semact-* quotedLit)

  field' : SemanticAction Concrete.Field Abstract.Field
  field' = semact-⊕ semact-underlying (semact-surround quotedField)

  nonemptyLine : SemanticAction Concrete.NonemptyLine Abstract.Line
  nonemptyLine =
    semact-map (uncurry _∷_) (semact-concat field'
      (semact-* (semact-right field')))

  nonemptyLine' : SemanticAction (Concrete.Field ⊗ ((literal ',' ⊗ Concrete.Field) *) ⊗ ε) Abstract.Line
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
  open import Test Unicode

  open DecodeUnicode Unicode Maybe.just

  s : String
  s = []

  p : Maybe.Maybe (literal '\"' s)
  p = runWeakParser Concrete.parseQuote s

  q : Maybe.Maybe (ε s)
  q = runWeakParser {g = ε} (Parser.pure (ε-intro)) s

  r = {!q!}

  csv1 : String
  csv1 = mkString "a,b,c\ne,f,g"

  csv1-cst : Maybe.Maybe (CST csv1)
  csv1-cst = runWeakParser concrete-parser csv1

  csv1-data : Maybe.Maybe AST
  csv1-data = runWeakParserΔ parser csv1

