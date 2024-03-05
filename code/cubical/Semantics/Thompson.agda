{-# OPTIONS --lossy-unification #-}
module Semantics.Thompson where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty.Base
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.W.Indexed
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.Instances.FreeComMonoid

open import Cubical.Tactics.Reflection
open import Semantics.Grammar
open import Semantics.NFA

private
  variable ℓ ℓ' : Level

module Thompson ℓ (Σ₀ : hSet ℓ) where
  open NFA ℓ Σ₀ public

  -- Thompson's construction for regular expressions
  -- I don't explicitly define the regular expression type,
  -- so I do this piecemeal for each constructor.

  isEquivalentNFA : (g : Grammar) → (N : NFA) → Type ℓ
  isEquivalentNFA g N = isEquivalentGrammar g (NFAGrammar N)

  equivalentNFA : (g : Grammar) → Type (ℓ-suc ℓ)
  equivalentNFA g = Σ[ N ∈ NFA ] (isEquivalentNFA g N)

  -- The empty regular expression
  ILin→emptyNFA : ParseTransformer ILin (NFAGrammar emptyNFA)
  ILin→emptyNFA {w} x =
    ε-cons (transport (cong (λ a → NFATrace emptyNFA _ a) (sym x)) nil)

  open NFA.NFA
  emptyNFATrace→ILin : ∀ {q w} → NFATrace emptyNFA q w → ILin w .fst
  emptyNFATrace→ILin NFA.nil = refl
  emptyNFATrace→ILin {q}{w} (NFA.ε-cons {w'}{t} x) = emptyNFATrace→ILin x

  emptyNFA→ILin : ParseTransformer (NFAGrammar emptyNFA) ILin
  emptyNFA→ILin {w} x = emptyNFATrace→ILin x

  open Iso
  -- equivalentILin : equivalentNFA ILin
  -- equivalentILin .fst = emptyNFA
  -- fun (equivalentILin .snd) = ILin→emptyNFA
  -- inv (equivalentILin .snd) = emptyNFA→ILin
  -- rightInv (equivalentILin .snd) b = {!!}
  -- leftInv (equivalentILin .snd) = {!!}

  -- The literal regular expression
  literal→literalNFA : ∀ {c} →
    ParseTransformer (literal c) (NFAGrammar (literalNFA c))
  literal→literalNFA {c} {w} x =
    transport
      (cong (λ a → NFATrace (literalNFA c) _ a) x)
      (NFATrace.cons {N = literalNFA c} nil)

  literalNFATraceElim : ∀ c q {w} →
    NFATrace (literalNFA c) q w → Σ[ g ∈ Grammar ] g w .fst
  literalNFATraceElim c .(literalNFA c .acc) NFA.nil = ILin , refl
  literalNFATraceElim c .(literalNFA c .init) (NFA.cons {w'} x) =
    literal c ⊗ literalNFATraceElim c (literalNFA c .acc) x .fst ,
    (([ c ] , w') , refl) , refl ,
      (literalNFATraceElim c (literalNFA c .acc) x .snd)

  open isSetNFATraceProof

  -- IW→literal : ∀ {c} {s}{w} → IWNFA (literalNFA c) (s , w) →  Σ[ g ∈ Grammar ] g w .fst
  -- IW→literal {c} {s} {w} (node (inl (s≡c , w≡mt)) subtree) = ILin , w≡mt
  -- IW→literal {c} {s} {w} (node (fsuc (inl ((t , p) , w' , c∷w'≡w))) subtree) =
    -- (literal c ⊗ IW→literal (subtree _) .fst) ,
      -- (([ c ] , w') , (sym (c∷w'≡w))) , refl , (IW→literal (subtree _) .snd)

  literalNFA→literal : ∀ {c} →
    ParseTransformer (NFAGrammar (literalNFA c)) (literal c)
  literalNFA→literal {c} {w} x = {!!}
    where
      x' : literalNFATraceElim c _ x .fst ≡ (literal c ⊗ {!!})
      x' = {!refl!}

  equivalentLiteral : (c : Σ₀ .fst) → equivalentNFA (literal c)
  equivalentLiteral c .fst = literalNFA c
  equivalentLiteral c .snd = {!!}

  -- The concatenation of regular expressions
  module _
    (g g' : Grammar)
    (eqg : equivalentNFA g)
    (eqg' : equivalentNFA g') where
    private
      N = eqg .fst
      N' = eqg' .fst
      M = ⊗NFA N N'
    open Iso
    open NFA.NFA
    N'Q→MQ : (q : N' .Q .fst) → M .Q .fst
    N'Q→MQ q = inr (inr (inl q))

    NQ→MQ : (q : N .Q .fst) → M .Q .fst
    NQ→MQ q = inr (inl q)

    N'Trace→MTrace : (q : N' .Q .fst) → (w : String) →
      NFATrace N' q w → NFATrace M (N'Q→MQ q) w
    N'Trace→MTrace .(N' .acc) .[] NFA.nil =
      ε-cons {t = inl (lift (fsuc (fsuc fzero)))} nil
    N'Trace→MTrace .(N' .src _) .(N' .label _ ∷ _) (NFA.cons {w'}{t} tr) =
      cons {t = fsuc t} (N'Trace→MTrace (N' .dst t) w' tr)
    N'Trace→MTrace .(N' .ε-src _) w (NFA.ε-cons {w'}{t} tr) =
      ε-cons {t = inr (inr t)} (N'Trace→MTrace (N' .ε-dst t) w' tr)

    NTrace→MTrace : (q : N .Q .fst) → (w w' : String) →
      NFATrace N q w →
      NFATrace M (N'Q→MQ (N' .init)) w' →
      NFATrace M (NQ→MQ q) (w ++ w')
    NTrace→MTrace .(N .acc) .[] w' NFA.nil trM =
      ε-cons {t = inl (lift (fsuc fzero))} trM
    NTrace→MTrace .(N .src _) .(N .label _ ∷ _) w' (NFA.cons {w}{t} x) trM =
      cons {t = inl t} (NTrace→MTrace (N .dst t) w w' x trM)
    NTrace→MTrace .(N .ε-src _) w w' (NFA.ε-cons {w}{t} x) trM =
      ε-cons {t = inr (inl t)}
        (NTrace→MTrace (N .ε-dst t) w w' x trM)

    g⊗g'→NFA : ParseTransformer (g ⊗ g') (NFAGrammar M)
    g⊗g'→NFA {w} (s , (p , p')) =
      ε-cons {t = inl (lift (inl _)) }
        (transport
          (cong (λ a → NFATrace M _ a) (sym (s .snd)))
          (NTrace→MTrace
            (N .init) (s .fst .fst) (s .fst .snd) (eqg .snd .fun p)
            (N'Trace→MTrace (N' .init) (s .fst .snd) (eqg' .snd .fun p'))))

    NFA→g⊗g' : ParseTransformer (NFAGrammar M) (g ⊗ g')
    NFA→g⊗g' {w} p = {!!}
