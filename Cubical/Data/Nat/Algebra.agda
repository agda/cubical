{-# OPTIONS --no-exact-split --safe #-}

{-

This file shows that the property of the natural numbers being a homotopy-initial algebra of
the functor (1 + _) is equivalent to fulfilling a closely related inductive elimination principle.

Proofing the latter is trivial, since the typechecker does the work for us.

For details see the paper [Homotopy-initial algebras in type theory](https://arxiv.org/abs/1504.05531)
by Steve Awodey, Nicola Gambino and Kristina Sojakova.

-}


module Cubical.Data.Nat.Algebra where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
  hiding (section)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Reflection.StrictEquiv

open import Cubical.Data.Nat.Base

private
  variable
    ℓ ℓ' : Level

record NatAlgebra ℓ : Type (ℓ-suc ℓ) where
  field
    Carrier  : Type ℓ
    alg-zero : Carrier
    alg-suc  : Carrier → Carrier

record NatMorphism (A : NatAlgebra ℓ) (B : NatAlgebra ℓ') : Type (ℓ-max ℓ ℓ') where
  open NatAlgebra
  field
    morph     : A .Carrier → B .Carrier
    comm-zero : morph (A .alg-zero) ≡ B .alg-zero
    comm-suc  : morph ∘ A .alg-suc ≡ B .alg-suc ∘ morph

record NatFiber (N : NatAlgebra ℓ') ℓ : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  open NatAlgebra N
  field
    Fiber    : Carrier → Type ℓ
    fib-zero : Fiber alg-zero
    fib-suc  : ∀ {n} → Fiber n → Fiber (alg-suc n)

record NatSection {N : NatAlgebra ℓ'} (F : NatFiber N ℓ) : Type (ℓ-max ℓ' ℓ) where
  open NatAlgebra N
  open NatFiber F
  field
    section       : ∀ n → Fiber n
    sec-comm-zero : section alg-zero ≡ fib-zero
    sec-comm-suc  : ∀ n → section (alg-suc n) ≡ fib-suc (section n)

isNatHInitial  : NatAlgebra ℓ' → (ℓ : Level) → Type (ℓ-max ℓ' (ℓ-suc ℓ))
isNatHInitial N ℓ = (M : NatAlgebra ℓ) → isContr (NatMorphism N M)

isNatInductive : NatAlgebra ℓ' → (ℓ : Level) → Type (ℓ-max ℓ' (ℓ-suc ℓ))
isNatInductive N ℓ = (S : NatFiber N ℓ) → NatSection S

module AlgebraPropositionality {N : NatAlgebra ℓ'} where
  open NatAlgebra N
  isPropIsNatHInitial : isProp (isNatHInitial N ℓ)
  isPropIsNatHInitial = isPropΠ (λ _ → isPropIsContr)

  -- under the assumption that some shape is nat-inductive, the type of sections over any fiber
  -- is propositional
  module SectionProp (ind : isNatInductive N ℓ) {F : NatFiber N ℓ} (S T : NatSection F) where
    open NatFiber
    open NatSection

    ConnectingFiber : NatFiber N ℓ
    Fiber ConnectingFiber n = S .section n ≡ T .section n
    fib-zero ConnectingFiber = S .sec-comm-zero ∙∙ refl ∙∙ sym (T .sec-comm-zero)
    fib-suc ConnectingFiber {n} sntn = S .sec-comm-suc n ∙∙ (λ i → F .fib-suc (sntn i)) ∙∙ sym (T .sec-comm-suc n)

    open NatSection (ind ConnectingFiber)
      renaming (section to α ; sec-comm-zero to ζ ; sec-comm-suc to σ)

    squeezeSquare : ∀{a}{A : Type a}{w x y z : A} (p : w ≡ x) {q : x ≡ y} (r : z ≡ y)
                  → (P : w ≡ z) → (sq : P ≡ p ∙∙ q ∙∙ sym r) → I → I → A
    squeezeSquare p {q} r P sq i j = transport (sym (PathP≡doubleCompPathʳ p P q r)) sq i j

    S≡T : S ≡ T
    section (S≡T i) n = α n i
    sec-comm-zero (S≡T i) j  = squeezeSquare (S .sec-comm-zero)  (T .sec-comm-zero)  (α alg-zero)    ζ     j i
    sec-comm-suc (S≡T i) n j = squeezeSquare (S .sec-comm-suc n) (T .sec-comm-suc n) (α (alg-suc n)) (σ n) j i

  isPropIsNatInductive : isProp (isNatInductive N ℓ)
  isPropIsNatInductive a b i F = SectionProp.S≡T a (a F) (b F) i

module AlgebraHInd→HInit {N : NatAlgebra ℓ'} (ind : isNatInductive N ℓ) (M : NatAlgebra ℓ) where
  open NatAlgebra
  open NatFiber

  ConstFiberM : NatFiber N ℓ
  Fiber ConstFiberM _ = M .Carrier
  fib-zero ConstFiberM = M .alg-zero
  fib-suc ConstFiberM = M .alg-suc

  morph→section : NatMorphism N M → NatSection ConstFiberM
  morph→section x = record { section = morph ; sec-comm-zero = comm-zero ; sec-comm-suc = λ i n → comm-suc n i }
    where open NatMorphism x
  section→morph : NatSection ConstFiberM → NatMorphism N M
  section→morph x = record { morph = section ; comm-zero = sec-comm-zero ; comm-suc = λ n i → sec-comm-suc i n }
    where open NatSection x

  Morph≡Section : NatSection ConstFiberM ≡ NatMorphism N M
  Morph≡Section = ua e
    where
    unquoteDecl e = declStrictEquiv e section→morph morph→section

  isContrMorph : isContr (NatMorphism N M)
  isContrMorph = subst isContr Morph≡Section (inhProp→isContr (ind ConstFiberM) (AlgebraPropositionality.SectionProp.S≡T ind))

open NatAlgebra
open NatFiber
open NatSection
open NatMorphism

module AlgebraHInit→Ind (N : NatAlgebra ℓ') ℓ (hinit : isNatHInitial N (ℓ-max ℓ' ℓ)) (F : NatFiber N (ℓ-max ℓ' ℓ)) where

  ΣAlgebra : NatAlgebra (ℓ-max ℓ' ℓ)
  Carrier ΣAlgebra = Σ (N .Carrier) (F .Fiber)
  alg-zero ΣAlgebra = N .alg-zero , F .fib-zero
  alg-suc ΣAlgebra (n , fn) = N .alg-suc n , F .fib-suc fn

  -- the fact that we have to lift the Carrier obstructs readability a bit
  -- this is the same algebra as N, but lifted into the correct universe
  LiftN : NatAlgebra (ℓ-max ℓ' ℓ)
  Carrier LiftN = Lift {_} {ℓ} (N .Carrier)
  alg-zero LiftN = lift (N .alg-zero)
  alg-suc LiftN = lift ∘ N .alg-suc ∘ lower

  _!_ : ∀ {x y} → x ≡ y → F .Fiber x → F .Fiber y
  _!_ = subst (F .Fiber)

  -- from homotopy initiality of N we get
  -- 1) an algebra morphism μ from N → Σ N F together with proofs of commutativity with the algebras
  -- 2) projecting out the first component after μ, called α, will turn out to be the identity function
  -- 3) witnesses that μ respects the definitions given in ΣAlgebra
  --   a) at zero the witnesses are ζ and ζ-h
  --   b) at suc the witnesses are σ and σ-h
  open NatMorphism (hinit ΣAlgebra .fst) renaming (morph to μ ; comm-zero to μ-zc ; comm-suc to μ-sc)
  module _ n where open Σ (μ n) public renaming (fst to α ; snd to α-h)
  -- module _ i where open Σ (μ-zc i) public renaming (fst to ζ ; snd to ζ-h)
  ζ   : α (N .alg-zero) ≡ N .alg-zero
  ζ i = μ-zc i .fst
  ζ-h : PathP (λ i → F .Fiber (ζ i)) (α-h (N .alg-zero)) (F .fib-zero)
  ζ-h i = μ-zc i .snd
  -- module _ n i where open Σ (μ-sc i n) public renaming (fst to σ ; snd to σ-h)
  σ   : ∀ n → α (N .alg-suc n) ≡ N .alg-suc (α n)
  σ n i = μ-sc i n .fst
  σ-h : ∀ n → PathP (λ i → F .Fiber (σ n i)) (α-h (N .alg-suc n)) (F .fib-suc (α-h n))
  σ-h n i = μ-sc i n .snd

  -- liftMorph would be the identity morphism if it weren't for size issues
  liftMorph : NatMorphism N LiftN
  liftMorph = record { morph = lift ; comm-zero = refl ; comm-suc = refl }
  -- instead of abstractly defining morphism composition and a projection algebra morphism
  -- from Σ N F → N, define the composite directly. comm-zero and comm-suc thus are
  -- defined without path composition
  fst∘μ : NatMorphism N LiftN
  morph fst∘μ = lift ∘ α
  comm-zero fst∘μ i = lift (ζ i)
  comm-suc fst∘μ i n = lift (σ n i)

  fst∘μ≡id : fst∘μ ≡ liftMorph
  fst∘μ≡id = isContr→isProp (hinit LiftN) _ _

  -- we get a proof that the index is preserved uniformly
  P : ∀ n → α n ≡ n
  P n i = lower (fst∘μ≡id i .morph n)

  -- we also have proofs that α cancels after the algebra of N
  Q-zero : α (N .alg-zero) ≡ N .alg-zero
  Q-zero = ζ
  Q-suc : ∀ n → α (N .alg-suc n) ≡ N .alg-suc n
  Q-suc n = σ n ∙ cong (N .alg-suc) (P n)

  -- but P and Q are the same up to homotopy
  P-zero : P (N .alg-zero) ≡ Q-zero
  P-zero i j = hcomp (λ k → λ where
      (i = i0) → lower (fst∘μ≡id j .comm-zero (~ k))
      (i = i1) → ζ (j ∨ ~ k)
      (j = i0) → ζ (~ k)
      (j = i1) → N .alg-zero
    ) (N .alg-zero)
  P-suc : ∀ n → P (N .alg-suc n) ≡ Q-suc n
  P-suc n i j = hcomp (λ k → λ where
      (i = i0) → lower (fst∘μ≡id j .comm-suc (~ k) n)
      (i = i1) → compPath-filler' (σ n) (cong (N .alg-suc) (P n)) k j
      (j = i0) → σ n (~ k)
      (j = i1) → N .alg-suc n
    ) (N .alg-suc (P n j))

  Fsection : NatSection F
  section Fsection n = P n ! α-h n
  sec-comm-zero Fsection =
    P (N .alg-zero) ! α-h (N .alg-zero)
      ≡[ i ]⟨ P-zero i ! α-h _ ⟩
    Q-zero ! α-h (N .alg-zero)
      ≡⟨ fromPathP ζ-h ⟩
    F .fib-zero
      ∎
  sec-comm-suc Fsection n =
    P (N .alg-suc n) ! α-h (N .alg-suc n)
      ≡[ i ]⟨ P-suc n i ! α-h _ ⟩
    Q-suc n ! α-h (N .alg-suc n)
      ≡⟨ substComposite (F .Fiber) (σ n) (cong (N .alg-suc) (P n)) _ ⟩
    cong (N .alg-suc) (P n) ! (σ n ! α-h (N .alg-suc n))
      ≡[ i ]⟨ cong (N .alg-suc) (P n) ! fromPathP (σ-h n) i ⟩
    cong (N .alg-suc) (P n) ! (F .fib-suc (α-h n))
      ≡⟨ substCommSlice (F .Fiber) (F .Fiber ∘ N .alg-suc) (λ _ → F .fib-suc) (P n) (α-h n) ⟩
    F .fib-suc (P n ! α-h n)
      ∎

isNatInductive≡isNatHInitial : {N : NatAlgebra ℓ'} (ℓ : Level)
                             → isNatInductive N (ℓ-max ℓ' ℓ) ≡ isNatHInitial N (ℓ-max ℓ' ℓ)
isNatInductive≡isNatHInitial {_} {N} ℓ = hPropExt isPropIsNatInductive isPropIsNatHInitial ind→init init→ind where
  open AlgebraPropositionality
  open AlgebraHInit→Ind N ℓ renaming (Fsection to init→ind)
  open AlgebraHInd→HInit renaming (isContrMorph to ind→init)

-- given two homotopy initial algebras there is a path between the algebras
-- this implies moreover that the carrier types are isomorphic
-- according to 5.16 in the paper this could be strengthened to isContr (N ≡ M)
isNatHInitial→algebraPath : {N M : NatAlgebra ℓ}
                          → (hinitN : isNatHInitial N ℓ) (hinitM : isNatHInitial M ℓ)
                          → N ≡ M
isNatHInitial→algebraPath {N = N} {M} hinitN hinitM = N≡M where
  open Σ (hinitN M) renaming (fst to N→M)
  open Σ (hinitM N) renaming (fst to M→N)
  idN : NatMorphism N N
  idN = record { morph = λ x → x ; comm-zero = refl ; comm-suc = refl }
  idM : NatMorphism M M
  idM = record { morph = λ x → x ; comm-zero = refl ; comm-suc = refl }
  N→M→N : NatMorphism N N
  morph N→M→N = morph M→N ∘ morph N→M
  comm-zero N→M→N = (λ i → morph M→N (comm-zero N→M i)) ∙ comm-zero M→N
  comm-suc N→M→N = (λ i → morph M→N ∘ comm-suc N→M i) ∙ (λ i → comm-suc M→N i ∘ morph N→M)
  nmn≡idn : N→M→N ≡ idN
  nmn≡idn = isContr→isProp (hinitN N) _ _

  M→N→M : NatMorphism M M
  morph M→N→M = morph N→M ∘ morph M→N
  comm-zero M→N→M = (λ i → morph N→M (comm-zero M→N i)) ∙ comm-zero N→M
  comm-suc M→N→M = (λ i → morph N→M ∘ comm-suc M→N i) ∙ (λ i → comm-suc N→M i ∘ morph M→N)
  mnm≡idm : M→N→M ≡ idM
  mnm≡idm = isContr→isProp (hinitM M) _ _

  carrier≡ : N .Carrier ≡ M .Carrier
  carrier≡ = isoToPath (iso (N→M .morph) (M→N .morph) (λ x i → mnm≡idm i .morph x) (λ x i → nmn≡idn i .morph x))
  zero≡ : PathP (λ i → carrier≡ i) (N .alg-zero) (M .alg-zero)
  zero≡ = toPathP λ i → transportRefl (N→M .comm-zero i) i
  suc≡ : PathP (λ i → carrier≡ i → carrier≡ i) (N .alg-suc) (M .alg-suc)
  suc≡ = toPathP (
        transport refl ∘ N→M .morph ∘ N .alg-suc ∘ M→N .morph ∘ transport refl
          ≡[ i ]⟨ transportReflF i ∘ N→M .morph ∘ N .alg-suc ∘ M→N .morph ∘ transportReflF i ⟩
        N→M .morph ∘ N .alg-suc ∘ M→N .morph
          ≡[ i ]⟨ N→M .comm-suc i ∘ M→N .morph ⟩
        M .alg-suc ∘ N→M .morph ∘ M→N .morph
          ≡[ i ]⟨ M .alg-suc ∘ mnm≡idm i .morph ⟩
        M .alg-suc
          ∎) where
     transportReflF : transport refl ≡ (λ x → x)
     transportReflF = funExt transportRefl

  N≡M : N ≡ M
  Carrier (N≡M i) = carrier≡ i
  alg-zero (N≡M i) = zero≡ i
  alg-suc (N≡M i) = suc≡ i

-- the payoff, it is straight forward to define the algebra and show inductiveness of ℕ
NatAlgebraℕ : NatAlgebra ℓ-zero
Carrier NatAlgebraℕ = ℕ
alg-zero NatAlgebraℕ = zero
alg-suc NatAlgebraℕ = suc

isNatInductiveℕ : isNatInductive NatAlgebraℕ ℓ
section (isNatInductiveℕ F) = nat-sec where
  nat-sec : ∀ n → F .Fiber n
  nat-sec zero = F .fib-zero
  nat-sec (suc n) = F .fib-suc (nat-sec n)
sec-comm-zero (isNatInductiveℕ F) = refl
sec-comm-suc (isNatInductiveℕ F) n = refl

isNatHInitialℕ : isNatHInitial NatAlgebraℕ ℓ
isNatHInitialℕ = transport (isNatInductive≡isNatHInitial _) isNatInductiveℕ
