open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.FinSet
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Unambiguous Alphabet
open import Term.Base Alphabet

open StrongEquivalence
module _ (c : ⟨ Alphabet ⟩) where
  module _ (c' : ⟨ Alphabet ⟩) where
    opaque
      unfolding _&_ literal
      same-literal : ＂ c ＂ & ＂ c' ＂ ⊢ ⊕[ x ∈ (c ≡ c') ] ＂ c ＂
      same-literal w (p , p') = c≡c' , p
        where
        c≡c' : c ≡ c'
        c≡c' = cons-inj₁ ((sym p) ∙ p')

  different-char : Grammar ℓ-zero
  different-char =
    ⊕[ c' ∈ ⟨ Alphabet ⟩ ] ⊕[ x ∈ (c ≡ c' → Empty.⊥ ) ] ＂ c' ＂

  disjoint-different-char : disjoint ＂ c ＂ different-char
  disjoint-different-char =
    ⊕ᴰ-elim (λ c' →
      ⊕ᴰ-elim (λ c≢c' → ⊕ᴰ-elim (λ c≡c' → Empty.rec (c≢c' c≡c')) ∘g same-literal c')
      ∘g &⊕ᴰ-distR≅ .fun
    )
    ∘g &⊕ᴰ-distR≅ .fun

  different-char→char : different-char ⊢ char
  different-char→char = ⊕ᴰ-elim (λ c' → ⊕ᴰ-elim λ _ → ⊕ᴰ-in c')

  different-starting-character : disjoint (char ⊗ string) (different-char ⊗ string)
  different-starting-character = {!!}

  different-char-in :
    {c' : ⟨ Alphabet ⟩} →
    (c ≡ c' → Empty.⊥) →
    literal c' ⊢ different-char
  different-char-in {c'} c≢c' = ⊕ᴰ-in c' ∘g ⊕ᴰ-in c≢c'

  literal-complement : Grammar ℓ-zero
  literal-complement =
    ε ⊕
    (different-char ⊗ string) ⊕
    (＂ c ＂ ⊗ (char +))

  literal-complement-empty? : literal-complement ⊢ ε ⊕ char +
  literal-complement-empty? =
    ⊕-elim
      ⊕-inl
      (⊕-elim
        (⊕-inr ∘g different-char→char ,⊗ id)
        (⊕-inr ∘g ⊕ᴰ-in c ,⊗ +→* char)
      )

  literal→char+ : ＂ c ＂ ⊢ char +
  literal→char+ = +-singleton char ∘g ⊕ᴰ-in c

  opaque
    unfolding &-intro ⊗-intro literal
    disjoint-literal-char⊗char+ : disjoint ＂ c ＂ (char ⊗ (char +))
    disjoint-literal-char⊗char+ w (pc , (s , (c' , pc') , (s' , (c'' , pc'') , str))) =
      Empty.rec (¬cons≡nil (cons-inj₂ ((sym w≡) ∙ w≡')))
      where
      w≡ : w ≡ c' ∷ [ c'' ] ++ s' .fst .snd
      w≡ =
        s .snd
        ∙ cong₂ _++_ pc' (s' .snd)
        ∙ cong (λ a → c' ∷ a ++ s' .fst .snd) pc''

      w≡' : w ≡ [ c ]
      w≡' = pc

  -- I really need better names
  disjoint-literal-begin-with-different : disjoint ＂ c ＂ (different-char ⊗ string)
  disjoint-literal-begin-with-different =
    ⊕-elim
      (disjoint-different-char ∘g id ,&p ⊗-unit-r)
      disjoint-literal-char⊗char+
    ∘g (id ,⊕p (id ,&p (different-char→char ,⊗ id)))
    ∘g &⊕-distL
    ∘g id ,&p (⊗⊕-distL ∘g id ,⊗ *≅ε⊕g⊗g* char .fun)

  disjoint-literal-complement : disjoint ＂ c ＂ literal-complement
  disjoint-literal-complement =
    ⊕-elim
      (disjoint-ε-char+ ∘g id ,&p (+-singleton char ∘g ⊕ᴰ-in c) ∘g &-swap)
      (⊕-elim
        disjoint-literal-begin-with-different
        (disjoint-literal-char⊗char+ ∘g id ,&p (⊕ᴰ-in c ,⊗ id))
      )
    ∘g (id ,⊕p &⊕-distL)
    ∘g &⊕-distL

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    unambiguous-literal-complement : unambiguous literal-complement
    unambiguous-literal-complement =
      unambiguous⊕
        (disjoint-ε-char+
        ∘g id ,&p ⊕-elim (different-char→char ,⊗ id) (+-cons char ∘g ⊕ᴰ-in c ,⊗ id))
        (unambiguousε isFinSetAlphabet)
        (unambiguous⊕
          (different-starting-character ∘g (⊕ᴰ-in c ,⊗ +→* char) ,&p id ∘g &-swap)
          {!!}
          {!!}
          isFinSetAlphabet)
        isFinSetAlphabet


    is-literal? : char ⊢ ＂ c ＂ ⊕ different-char
    is-literal? = ⊕ᴰ-elim λ c' →
      decRec
        (λ c≡c' → ⊕-inl ∘g transportG (cong literal (sym c≡c')))
        (λ c≢c' → ⊕-inr ∘g different-char-in c≢c')
        ((isFinSet→Discrete isFinSetAlphabet) c c')

    opaque
      unfolding _⊕_ ε literal
      parse-literal :
        string ⊢ ＂ c ＂ ⊕ literal-complement
      parse-literal =
        rec (*Ty char)
        (λ _ → ⊕ᴰ-elim λ {
          nil → ⊕-inr ∘g ⊕-inl ∘g lowerG ∘g lowerG
        ; cons →
          ⊕-elim
            (
            ⊕-elim
              ⊕-inl
              (⊕-inr ∘g ⊕-inr ∘g ⊕-inl ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻)
            ∘g is-literal?
            ∘g ⊗-unit-r)
            (⊕-inr
            ∘g ⊕-elim
              (⊕-inr ∘g ⊕-inr)
              (⊕-inr ∘g ⊕-inl ∘g id ,⊗ +→* char)
            ∘g ⊗⊕-distR
            ∘g is-literal? ,⊗ id
            )
          ∘g ⊗⊕-distL
          ∘g id ,⊗ ⊕-elim (⊕-inr ∘g literal→char+) literal-complement-empty?
          ∘g (lowerG ,⊗ lowerG)
        })
        _

    open StrongEquivalence
    totallyParseableLiteral : totallyParseable ＂ c ＂
    totallyParseableLiteral .fst = literal-complement
    totallyParseableLiteral .snd .fun = ⊤-intro
    totallyParseableLiteral .snd .inv = parse-literal ∘g ⊤→string
    totallyParseableLiteral .snd .sec = unambiguous⊤ _ _
    totallyParseableLiteral .snd .ret = {!!}

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    unambiguous-literal : unambiguous ＂ c ＂
    unambiguous-literal = ans
      where
      opaque
        unfolding literal
        ans : unambiguous ＂ c ＂
        ans = EXTERNAL.isLang→unambiguous isFinSetAlphabet λ w → isSetString _ _
