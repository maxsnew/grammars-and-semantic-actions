open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
import Cubical.Data.Equality as Eq
open import Term Alphabet
open import Helper

private
  variable ℓN ℓN' ℓP ℓ : Level

record NFA ℓN : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN
    init : Q .fst
    isAcc : Q .fst → Bool
    transition : FinSet ℓN
    src : ⟨ transition ⟩ → ⟨ Q ⟩
    dst : ⟨ transition ⟩ → ⟨ Q ⟩
    label : ⟨ transition ⟩ → ⟨ Alphabet ⟩
    ε-transition : FinSet ℓN
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩

  decEqQ : Discrete ⟨ Q ⟩
  decEqQ = isFinSet→Discrete (str Q)

  hasTransition : Discrete ⟨ Alphabet ⟩ → ⟨ Q ⟩ →
    ⟨ Alphabet ⟩ → ⟨ Q ⟩ → DecProp ℓN
  hasTransition discAlphabet src' label' dst' =
    DecProp∃ transition (λ t →
      DecProp×
         (DecProp≡ (discreteLift {L' = ℓN} discAlphabet)
           (lift label') (lift (label t)))
         (DecProp×
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift src') (lift (src t)))
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift dst') (lift (dst t)))
          ))

  data Tag : Type ℓN where
    stop step stepε : Tag

  TraceTy : Bool → (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) (λ
        (lift acc) → k (LiftG ℓN ε) )
    ; step → ⊕e (Eq.fiber src q) λ {
        (t , Eq.refl ) →
          ⊗e (k (LiftG ℓN (literal (label t)))) (Var (dst t)) }
    ; stepε → ⊕e (Eq.fiber ε-src q) λ { (t , Eq.refl) → Var (ε-dst t) } }

  Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓN
  Trace b = μ (TraceTy b)

-- record NFA : Type (ℓ-suc ℓN) where
--   field
--     Q : FinSet ℓN
--     init : Q .fst
--     isAcc : Q .fst → DecProp ℓN
--     transition : FinSet ℓN
--     src : ⟨ transition ⟩ → ⟨ Q ⟩
--     dst : ⟨ transition ⟩ → ⟨ Q ⟩
--     label : ⟨ transition ⟩ → ⟨ Alphabet ⟩
--     ε-transition : FinSet ℓN
--     ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
--     ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩

--   decEqQ : Discrete ⟨ Q ⟩
--   decEqQ = isFinSet→Discrete (str Q)

--   hasTransition : Discrete ⟨ Alphabet ⟩ → ⟨ Q ⟩ →
--     ⟨ Alphabet ⟩ → ⟨ Q ⟩ → DecProp ℓN
--   hasTransition discΣ₀ src' label' dst' =
--     DecProp∃ transition (λ t →
--       DecProp×
--          (LiftDecProp {ℓ-zero} {ℓN} (DecProp≡ discΣ₀ label' (label t)))
--          (DecProp×
--            (DecProp≡ decEqQ src' (src t))
--            (DecProp≡ decEqQ dst' (dst t))))

--   -- The grammar "Parse q" denotes the type of traces in the NFA
--   -- from state q to an accepting state
--   data Parse : (q : ⟨ Q ⟩) → Grammar ℓN where
--     nil : ∀ {q} → isAcc q .fst .fst →
--       ε ⊢ Parse q
--     cons : ∀ tr →
--       literal (label tr) ⊗' Parse (dst tr) ⊢ Parse (src tr)
--     ε-cons : ∀ εtr →
--       Parse (ε-dst εtr) ⊢ Parse (ε-src εtr)

--   InitParse : Grammar ℓN
--   InitParse = Parse init

--   record Algebra : Typeω where
--     field
--       the-ℓs : ⟨ Q ⟩ → Level
--       G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
--       nil-case : ∀ {q} → isAcc q .fst .fst →
--         ε ⊢ G q
--       cons-case : ∀ tr →
--         literal (label tr) ⊗ G (dst tr) ⊢ G (src tr)
--       ε-cons-case : ∀ εtr →
--         G (ε-dst εtr) ⊢ G (ε-src εtr)

--   open Algebra

--   opaque
--     unfolding _⊗_
--     initial : Algebra
--     the-ℓs initial _ = ℓN
--     G initial = Parse
--     nil-case initial = nil
--     cons-case initial = cons
--     ε-cons-case initial = ε-cons

--   record AlgebraHom (alg alg' : Algebra) : Typeω where
--     field
--       f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
--       on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
--         f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
--       on-cons : (tr : ⟨ transition ⟩) →
--         f (src tr) ∘g alg .cons-case tr ≡
--           alg' .cons-case tr ∘g (⊗-intro id (f (dst tr)))
--       on-ε-cons : (εtr : ⟨ ε-transition ⟩) →
--         (f (ε-src εtr)) ∘g (alg .ε-cons-case εtr) ≡
--           alg' .ε-cons-case εtr ∘g f (ε-dst εtr)
--     fInit = f init

--   open AlgebraHom

--   opaque
--     unfolding ⊗-intro
--     idAlgebraHom : (alg : Algebra) →
--       AlgebraHom alg alg
--     f (idAlgebraHom alg) q = id
--     on-nil (idAlgebraHom alg) _ = refl
--     on-cons (idAlgebraHom alg) _ = refl
--     on-ε-cons (idAlgebraHom alg) _ = refl

--     AlgebraHom-seq : {alg alg' alg'' : Algebra} →
--       AlgebraHom alg alg' → AlgebraHom alg' alg'' →
--       AlgebraHom alg alg''
--     f (AlgebraHom-seq ϕ ψ) q _ x =
--       ψ .f q _ (ϕ .f q _ x)
--     on-nil (AlgebraHom-seq ϕ ψ) qAcc =
--       cong (λ t → t ⋆ ψ .f _) (ϕ .on-nil qAcc) ∙
--       ψ .on-nil qAcc
--     on-cons (AlgebraHom-seq ϕ ψ) tr =
--       cong (λ t → t ⋆ ψ .f (src tr)) (ϕ .on-cons tr) ∙
--       cong (λ t → ⊗-intro id (ϕ .f (dst tr)) ⋆ t) (ψ .on-cons tr)
--     on-ε-cons (AlgebraHom-seq ϕ ψ) εtr =
--       cong (λ t → t ⋆ ψ .f (ε-src εtr)) (ϕ .on-ε-cons εtr) ∙
--       cong (λ t → ϕ .f (ε-dst εtr)⋆ t) (ψ .on-ε-cons εtr)

--   module _
--     (the-alg : Algebra)
--     where
--     opaque
--       unfolding _⊗_
--       recTrace : ∀ {q} → Parse q ⊢ the-alg .G q
--       recTrace _ (nil qAcc _ pε) = the-alg .nil-case qAcc _ pε
--       recTrace _ (cons tr _ p⊗) =
--         the-alg .cons-case tr _
--           ((p⊗ .fst) , ((p⊗ .snd .fst) , (recTrace _ (p⊗ .snd .snd))))
--       recTrace _ (ε-cons εtr _ p) =
--         the-alg .ε-cons-case εtr _ (recTrace _ p)

--     recInit : Parse init ⊢ the-alg .G init
--     recInit = recTrace

--     opaque
--       unfolding recTrace ⊗-intro initial _⊗_
--       ∃AlgebraHom : AlgebraHom initial the-alg
--       f ∃AlgebraHom q = recTrace {q}
--       on-nil ∃AlgebraHom _ = refl
--       on-cons ∃AlgebraHom _ = refl
--       on-ε-cons ∃AlgebraHom _ = refl

--       !AlgebraHom-help :
--         (e e' : AlgebraHom initial the-alg) →
--         (q : Q .fst) →
--         (∀ w p → e .f q w p ≡ e' .f q w p)
--       !AlgebraHom-help e e' q w (nil qAcc .w pε) =
--         cong (λ a → a w pε) (e .on-nil qAcc) ∙
--         sym (cong (λ a → a w pε) (e' .on-nil qAcc))
--       !AlgebraHom-help e e' .(src tr) w (cons tr .w p⊗) =
--         cong (λ a → a w p⊗) (e .on-cons tr) ∙
--         cong (λ a → the-alg .cons-case tr _
--           ((p⊗ .fst) , ((p⊗ .snd .fst) , a)))
--           (!AlgebraHom-help e e' (dst tr) _
--             (p⊗ .snd .snd)) ∙
--         sym (cong (λ a → a w p⊗) (e' .on-cons tr))
--       !AlgebraHom-help e e' .(ε-src εtr) w (ε-cons εtr .w p) =
--         cong (λ a → a w p) (e .on-ε-cons εtr) ∙
--         cong (the-alg .ε-cons-case εtr w)
--           (!AlgebraHom-help e e' (ε-dst εtr) _ p) ∙
--         sym (cong (λ a → a w p) (e' . on-ε-cons εtr))

--     !AlgebraHom :
--       (e e' : AlgebraHom initial the-alg) →
--       (q : Q .fst) →
--       e .f q ≡ e' .f q
--     !AlgebraHom e e' q =
--       funExt (λ w → funExt (λ p → !AlgebraHom-help e e' q w p))

--   opaque
--     unfolding idAlgebraHom
--     initial→initial≡id :
--       (e : AlgebraHom initial initial) →
--       (q : Q .fst) →
--       (e .f q)
--         ≡
--       id
--     initial→initial≡id e q =
--       !AlgebraHom initial e (idAlgebraHom initial) q

--   algebra-η :
--     (e : AlgebraHom initial initial) →
--     fInit e ≡ id
--   algebra-η e = initial→initial≡id e _

--   -- Often it is convenient to do a recursion on something with other
--   -- variables in scope. For this we develop the notion of a
--   -- *parameterized* algebra, where we have an additional parameter
--   -- that has to be consumed in the base case. In general we could
--   -- have two parameters: a left and right parameter, but this is the
--   -- only one we need so far.
--   module _ {ℓp} (P : Grammar ℓp) where
--     record PAlgebra : Typeω where
--       field
--         the-ℓs : Q .fst → Level
--         G : (q : Q .fst) → Grammar (the-ℓs q)
--         nil-case : ∀ {q} → isAcc q .fst .fst →
--           P ⊢ G q
--         cons-case : ∀ tr →
--           (literal (label tr) ⊗ G (dst tr)) ⊢ G (src tr)
--         ε-cons-case : ∀ εtr →
--           G (ε-dst εtr) ⊢ G (ε-src εtr)

--     open PAlgebra

--     opaque
--       unfolding _⊗_
--       P-initial : PAlgebra
--       P-initial .the-ℓs = _
--       P-initial .G q = Parse q ⊗ P
--       P-initial .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
--       P-initial .cons-case tr = ⊗-intro (cons tr) id ∘g ⊗-assoc
--       P-initial .ε-cons-case tr = ⊗-intro (ε-cons tr) id

--     record PAlgebraHom (alg alg' : PAlgebra) : Typeω where
--       field
--         f : (q : Q .fst) → alg .G q ⊢ alg' .G q
--         on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
--           f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
--         on-cons : (tr : transition .fst) →
--           f (src tr) ∘g alg .cons-case tr ≡
--             alg' .cons-case tr ∘g (⊗-intro id (f (dst tr)))
--         on-ε-cons : (εtr : ε-transition .fst) →
--           (f (ε-src εtr)) ∘g (alg .ε-cons-case εtr) ≡
--             alg' .ε-cons-case εtr ∘g f (ε-dst εtr)

--     open PAlgebraHom

--     opaque
--       unfolding _⊗_ ⊗-intro
--       P-idAlgebraHom : (alg : PAlgebra) → PAlgebraHom alg alg
--       P-idAlgebraHom alg .f _ = id
--       P-idAlgebraHom alg .on-nil _ = refl
--       P-idAlgebraHom alg .on-cons _ = refl
--       P-idAlgebraHom alg .on-ε-cons _ = refl

--       PAlgebraHom-seq : {alg alg' alg'' : PAlgebra} →
--         PAlgebraHom alg alg' → PAlgebraHom alg' alg'' →
--         PAlgebraHom alg alg''
--       PAlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
--       PAlgebraHom-seq ϕ ψ .on-nil qAcc =
--         cong (ψ .f _ ∘g_) (ϕ .on-nil qAcc) ∙
--         ψ .on-nil qAcc
--       PAlgebraHom-seq ϕ ψ .on-cons t =
--         cong (ψ .f (src t) ∘g_) (ϕ .on-cons t) ∙
--         cong (_∘g ⊗-intro id (ϕ .f (dst t))) (ψ .on-cons t)
--       PAlgebraHom-seq ϕ ψ .on-ε-cons t =
--         cong (ψ .f (ε-src t) ∘g_) (ϕ .on-ε-cons t) ∙
--         cong (_∘g ϕ .f (ε-dst t)) (ψ .on-ε-cons t)

--     module _ (the-p-alg : PAlgebra) where
--       underlyingAlg : Algebra
--       underlyingAlg .the-ℓs = _
--       underlyingAlg .G q = (the-p-alg .G q) ⟜ P
--       underlyingAlg .nil-case qAcc =
--         ⟜-intro ((the-p-alg .nil-case qAcc) ∘g ⊗-unit-l)
--       underlyingAlg .cons-case t =
--          ⟜-intro ((the-p-alg .cons-case t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)
--       underlyingAlg .ε-cons-case t =
--          ⟜-intro ((the-p-alg .ε-cons-case t) ∘g ⟜-app)

--       P-recTrace : ∀ {q} → Parse q ⊗ P ⊢ the-p-alg .G q
--       P-recTrace = ⟜-app ∘g ⊗-intro (recTrace underlyingAlg) id

--       P-recInit : InitParse ⊗ P ⊢ the-p-alg .G init
--       P-recInit = P-recTrace

--       opaque
--         unfolding ∃AlgebraHom P-initial
--         ∃PAlgebraHom : PAlgebraHom P-initial the-p-alg
--         ∃PAlgebraHom .f q = P-recTrace
--         ∃PAlgebraHom .on-nil qAcc =
--           (λ i → ⟜-app ∘g ⊗-intro (∃AlgebraHom underlyingAlg .on-nil qAcc i) id
--             ∘g ⊗-unit-l⁻) ∙
--           (λ i → ⟜-β (the-p-alg .nil-case qAcc ∘g ⊗-unit-l) i ∘g ⊗-unit-l⁻) ∙
--           (λ i → the-p-alg .nil-case qAcc ∘g ⊗-unit-l⁻l i)
--         ∃PAlgebraHom .on-cons t =
--           (λ i → ⟜-β ((the-p-alg .cons-case t) ∘g
--             ⊗-intro id ⟜-app ∘g ⊗-assoc⁻) i ∘g
--             ⊗-intro (⊗-intro id (recTrace underlyingAlg)) id ∘g ⊗-assoc) ∙
--             (λ i → the-p-alg .cons-case t ∘g ⊗-intro id P-recTrace ∘g
--               ⊗-assoc⁻∘⊗-assoc≡id i)
--         ∃PAlgebraHom .on-ε-cons t =
--           (λ i → ⟜-β ((the-p-alg .ε-cons-case t) ∘g ⟜-app) i ∘g
--             ⊗-intro (recTrace underlyingAlg) id)

--         curryPAlg :
--           PAlgebraHom P-initial the-p-alg → AlgebraHom initial underlyingAlg
--         curryPAlg e .f q = ⟜-intro (e .f q)
--         curryPAlg e .on-nil acc =
--           isoFunInjective (invIso ⟜UMP) _ _
--             ((λ i → ⟜-β (e .f _) i ∘g ⊗-intro (nil acc) id)
--             ∙ (λ i → e .f _ ∘g ⊗-intro (nil acc) id ∘g ⊗-unit-ll⁻ (~ i))
--             ∙ (λ i → e .on-nil acc i ∘g ⊗-unit-l)
--             ∙ sym (⟜-β (the-p-alg .nil-case acc ∘g ⊗-unit-l))
--             )
--         curryPAlg e .on-cons t = isoFunInjective (invIso ⟜UMP) _ _
--           ( ((λ i → ⟜-β (e .f _) i ∘g ⊗-intro (cons t) id))
--           ∙ (λ i → e .f (src t) ∘g
--                ⊗-intro (cons t) id ∘g ⊗-assoc∘⊗-assoc⁻≡id (~ i))
--           ∙ (λ i → e .on-cons t i ∘g ⊗-assoc⁻)
--           ∙ (λ i → the-p-alg .cons-case t ∘g
--                ⊗-intro id (⟜-β (e .f (dst t)) (~ i)) ∘g ⊗-assoc⁻)
--           ∙ (λ i → ⟜-β (the-p-alg .cons-case t ∘g
--                           ⊗-intro id ⟜-app ∘g ⊗-assoc⁻) (~ i) ∘g
--                     ⊗-intro (⊗-intro id (⟜-intro (e .f (dst t)))) id))
--         curryPAlg e .on-ε-cons t = isoFunInjective (invIso ⟜UMP) _ _
--           ((((λ i → ⟜-β (e .f _) i ∘g ⊗-intro (ε-cons t) id)))
--           ∙ e .on-ε-cons t
--           ∙ (λ i → the-p-alg .ε-cons-case t ∘g ⟜-β (e .f (ε-dst t)) (~ i))
--           ∙ (λ i → ⟜-β (the-p-alg .ε-cons-case t ∘g ⟜-app) (~ i) ∘g
--                           ⊗-intro (⟜-intro (e .f (ε-dst t))) id))

--         !PAlgebraHom' :
--           (e e' : PAlgebraHom P-initial the-p-alg) →
--           (q : Q .fst) →
--           e .f q ≡ e' .f q
--         !PAlgebraHom' e e' q =
--           isoFunInjective ⟜UMP _ _ (!AlgebraHom underlyingAlg
--             (curryPAlg e)
--             (curryPAlg e')
--             q)

--         -- Need to contort things a bit to convince Agda we're terminating
--         PrT-helper :
--           ∀ {q}{wl} →
--           Parse q wl →
--           ∀ {w}{wr} → (w ≡ wl ++ wr) → P wr → the-p-alg .G q w
--         PrT-helper (nil acc _ wl≡[]) splits p =
--           (the-p-alg .nil-case acc ∘g ⊗-unit-l)
--             _ ((_ , splits) , (wl≡[] , p))
--         PrT-helper {wl = wl}
--           (cons tr _ (split' , lit , parse)) {w = w}{wr = wr} splits p =
--           the-p-alg .cons-case tr _ ((_ , pf) ,
--             (lit , (PrT-helper parse refl p)))
--           where
--             pf : w ≡ split' .fst .fst ++ split' .fst .snd ++ wr
--             pf = splits ∙ cong (_++ wr) (split' .snd) ∙
--               ++-assoc (split' .fst .fst) _ wr
--         PrT-helper (ε-cons εtr _ parse) splits p =
--           the-p-alg .ε-cons-case εtr _ (PrT-helper parse splits p)

--         -- A direct definition that doesn't use function types
--         -- defining equations (all hold by refl)
--         P-recTrace' : ∀ {q} → Parse q ⊗ P ⊢ the-p-alg .G q
--         P-recTrace' w (splitting , parse , p) =
--           PrT-helper parse (splitting .snd) p

--         -- P-recTrace'-nil-test :
--         --   ∀ {q}{acc : ⟨ isAcc q .fst ⟩ } →
--         --   P-recTrace' ∘g ⊗-intro (nil acc) id
--         --   ≡ the-p-alg .nil-case acc ∘g ⊗-unit-l
--         -- P-recTrace'-nil-test = refl

--         -- P-recTrace'-cons-test :
--         --   ∀ {tr : ⟨ transition ⟩ } →
--         --   P-recTrace' ∘g ⊗-intro (cons tr) id
--         --   ≡ the-p-alg .cons-case tr ∘g ⊗-intro id P-recTrace' ∘g ⊗-assoc⁻
--         -- P-recTrace'-cons-test = refl

--         -- P-recTrace'-ε-cons-test :
--         --   ∀ {εtr : ⟨ ε-transition ⟩} →
--         --   P-recTrace' ∘g (⊗-intro (ε-cons εtr) id)
--         --   ≡ the-p-alg .ε-cons-case εtr ∘g P-recTrace'
--         -- P-recTrace'-ε-cons-test = refl

--       -- Agda can't figure out this definition is terminating unfortunately
--       -- P-recTrace' w ((([]' , w'), splits) , nil acc ._ []'≡[] , p) =
--       --   (the-p-alg .nil-case acc ∘g ⊗-unit-l) w ((_ , splits) , ([]'≡[] , p))
--       -- --
--       -- P-recTrace' w (split , cons tr _ (split' , lit , parse) , p) =
--       --   the-p-alg .cons-case tr _
--         --   ((_ , split .snd ∙ cong (_++ split .fst .snd) (split' .snd) ∙
--         --     ++-assoc (split' .fst .fst)
--         --       (split' .fst .snd) (split .fst .snd)) , (lit ,
--       --     (P-recTrace' _ ((_ , refl) , (parse , p))))) --
--       --   -- (⊗-intro id P-recTrace' _ {!!})
--       --     -- (⊗-assoc⁻ _ ((split , ((split' , (lit , parse)) , p)))))
--       --   -- (the-p-alg .cons-case tr ∘g ⊗-intro id P-recTrace' ∘g ⊗-assoc⁻)
--       --   --   w
--       --   -- the-p-alg .cons-case tr _ {!P-recTrace' _ (? , parse , p)!}
--       --   -- where

--       -- definitional equation 2:
--       -- P-recTrace' ∘g ε-cons εtr ≡ the-p-alg .ε-cons-case εtr ∘g P-recTrace'
--       --  (the-p-alg .ε-cons-case εtr ∘g P-recTrace') w (split , (parse , p))
--       -- P-recTrace' w (split , ε-cons εtr _ parse , p) =
--       --   the-p-alg .ε-cons-case εtr _ (P-recTrace' _ (split , parse , p))

--       P-recInit' : InitParse ⊗ P ⊢ the-p-alg .G init
--       P-recInit' = P-recTrace'

--       opaque
--         unfolding P-recTrace'
--         ∃PAlgebraHom' : PAlgebraHom P-initial the-p-alg
--         ∃PAlgebraHom' .f = λ q → P-recTrace'
--         -- would be refl with an equiv defn of PAlgebraHom
--         ∃PAlgebraHom' .on-nil qAcc =
--           λ i → the-p-alg .nil-case qAcc ∘g (⊗-unit-l⁻l i)
--         -- these would be refl if we changed the definition of PAlgebraHom to pu
--         ∃PAlgebraHom' .on-cons tr =
--           λ i → the-p-alg .cons-case tr ∘g
--             ⊗-intro id P-recTrace' ∘g ⊗-assoc⁻∘⊗-assoc≡id i
--         ∃PAlgebraHom' .on-ε-cons εtrans = refl

--         -- This justifies that adding P-recTrace' is a
--         -- conservative extension of our type theory
--         P-recTrace'-conservative-extension :
--           ∀ {q} → P-recTrace {q = q} ≡ P-recTrace' {q = q}
--         P-recTrace'-conservative-extension =
--           !PAlgebraHom' ∃PAlgebraHom ∃PAlgebraHom' _
