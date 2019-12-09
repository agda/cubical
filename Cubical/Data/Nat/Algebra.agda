{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Algebra where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
  hiding (section)

open import Cubical.Data.Nat.Base

record NatAlgebra ℓ : Set (ℓ-suc ℓ) where
  field
    Carrier  : Set ℓ
    alg-zero : Carrier
    alg-suc  : Carrier → Carrier

record NatMorphism {ℓ ℓ'} (A : NatAlgebra ℓ) (B : NatAlgebra ℓ') : Set (ℓ-max ℓ ℓ') where
  open NatAlgebra
  field
    morph     : A .Carrier → B .Carrier
    comm-zero : morph (A .alg-zero) ≡ B .alg-zero
    comm-suc  : morph ∘ A .alg-suc ≡ B .alg-suc ∘ morph

record NatFiber {ℓ'} (N : NatAlgebra ℓ') ℓ : Set (ℓ-max ℓ' (ℓ-suc ℓ)) where
  open NatAlgebra N
  field
    Fiber    : Carrier → Set ℓ
    fib-zero : Fiber alg-zero
    fib-suc  : ∀ {n} → Fiber n → Fiber (alg-suc n)

record NatSection {ℓ' ℓ}{N : NatAlgebra ℓ'} (F : NatFiber N ℓ) : Set (ℓ-max ℓ' ℓ) where
  open NatAlgebra N
  open NatFiber F
  field
    section       : ∀ n → Fiber n
    sec-comm-zero : section alg-zero ≡ fib-zero
    sec-comm-suc  : ∀ n → section (alg-suc n) ≡ fib-suc (section n)

isNatHInitial  : ∀ {ℓ'} → NatAlgebra ℓ' → (ℓ : Level) → Set _
isNatHInitial N ℓ = (M : NatAlgebra ℓ) → isContr (NatMorphism N M)

isNatInductive : ∀ {ℓ'} → NatAlgebra ℓ' → (ℓ : Level) → Set _
isNatInductive N ℓ = (S : NatFiber N ℓ) → NatSection S

module AlgebraPropositionality {ℓ ℓ'} {N : NatAlgebra ℓ'} where
  open NatAlgebra N
  isPropIsNatHInitial : isProp (isNatHInitial N ℓ)
  isPropIsNatHInitial = propPi (λ _ → isPropIsContr)

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

    squeezeSquare : ∀{a}{A : Set a}{w x y z : A} (p : w ≡ x) {q : x ≡ y} (r : z ≡ y)
                  → (P : w ≡ z) → (sq : P ≡ p ∙∙ q ∙∙ sym r) → I → I → A
    squeezeSquare p {q} r P sq i j = hcomp (λ k → λ where
        (i = i0) → P j
        (i = i1) → doubleCompPath-filler p q (sym r) j (~ k)
        (j = i0) → p (k ∧ i)
        (j = i1) → r (k ∧ i)
      ) (sq i j)

    S≡T : S ≡ T
    section (S≡T i) n = α n i
    sec-comm-zero (S≡T i) j  = squeezeSquare (S .sec-comm-zero)  (T .sec-comm-zero)  (α alg-zero)    ζ     j i
    sec-comm-suc (S≡T i) n j = squeezeSquare (S .sec-comm-suc n) (T .sec-comm-suc n) (α (alg-suc n)) (σ n) j i

  isPropIsNatInductive : isProp (isNatInductive N ℓ)
  isPropIsNatInductive a b i F = SectionProp.S≡T a (a F) (b F) i

module AlgebraHInd→HInit {ℓ' ℓ} {N : NatAlgebra ℓ'} (ind : isNatInductive N ℓ) (M : NatAlgebra ℓ) where
  open NatAlgebra
  open NatFiber

  ConstFiberM : NatFiber N ℓ
  Fiber ConstFiberM n = M .Carrier
  fib-zero ConstFiberM = M .alg-zero
  fib-suc ConstFiberM = M .alg-suc

  morph→section : NatMorphism N M → NatSection ConstFiberM
  morph→section x = record { section = morph ; sec-comm-zero = comm-zero ; sec-comm-suc = λ i n → comm-suc n i } where open NatMorphism x
  section→morph : NatSection ConstFiberM → NatMorphism N M
  section→morph x = record { morph = section ; comm-zero = sec-comm-zero ; comm-suc = λ n i → sec-comm-suc i n } where open NatSection x
  Morph≡Section : NatSection ConstFiberM ≡ NatMorphism N M
  Morph≡Section = isoToPath (iso section→morph morph→section (λ _ → refl) (λ _ → refl))

  isContrMorph : isContr (NatMorphism N M)
  isContrMorph = subst isContr Morph≡Section (inhProp→isContr (ind ConstFiberM) (AlgebraPropositionality.SectionProp.S≡T ind))

apP : ∀ {a b} {A : Set a} {B : A → Set b} (f : (a : A) → B a) → {x y : A} → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
apP f p i = f (p i)

module Helper {a b} {A : Set a} (B : A → Set b) where
  _!_ : ∀ {x y} → x ≡ y → B x → B y
  _!_ = subst B

  -- substituting commutes with maps in slices
  module SubstProperties (f : A → A) (F : ∀ i → B i → B (f i)) {n m : A} {p : n ≡ m} {u : B n} where
    pathA : I → Type b
    pathA i = apP (B ∘ f) p i
    pathB : I → Type b
    pathB i = apP B p i

    substDepends : (apP f p ! F n u) ≡ F m (p ! u)
    substDepends i = comp pathA (λ k → λ where
        (i = i0) → toPathP {A = pathA} (λ _ → apP f p ! F n u) k
        (i = i1) → F (p k) (toPathP {A = pathB} (λ _ → p ! u) k)
      ) (F n u)

  -- transporting along a composite is the same as transporting twice
  module CompProperties {x y z : A} (p : x ≡ y) (q : y ≡ z) where
    compSq : I → I → A
    compSq = compPath'-filler p q
    precomposite : ∀ {Bx} → refl ! ((p □ q) ! Bx) ≡ q ! (p ! Bx)
    precomposite {Bx} i = transp (λ k → B (compSq (~ i ∧ ~ k) (~ i ∨ k))) i0 (transp (λ k → B (compSq (~ i ∨ ~ k) (~ i ∧ k))) i0 Bx)

    composite : ∀ {Bx} → (p □ q) ! Bx ≡ q ! (p ! Bx)
    composite = sym (substRefl {B = B} _) ∙ precomposite

open NatAlgebra
open NatFiber
open NatSection
open NatMorphism

module AlgebraHInit→Ind {ℓ'} (N : NatAlgebra ℓ') ℓ (hinit : isNatHInitial N (ℓ-max ℓ' ℓ)) (F : NatFiber N (ℓ-max ℓ' ℓ)) where

  ΣAlgebra : NatAlgebra (ℓ-max ℓ' ℓ)
  Carrier ΣAlgebra = Σ (N .Carrier) (F .Fiber)
  alg-zero ΣAlgebra = N .alg-zero , F .fib-zero
  alg-suc ΣAlgebra (n , fn) = N .alg-suc n , F .fib-suc fn

  LiftN : NatAlgebra (ℓ-max ℓ' ℓ)
  Carrier LiftN = Lift {_} {ℓ} (N .Carrier)
  alg-zero LiftN = lift (N .alg-zero)
  alg-suc LiftN = lift ∘ N .alg-suc ∘ lower

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

  liftMorph : NatMorphism N LiftN
  liftMorph = record { morph = lift ; comm-zero = refl ; comm-suc = refl }
  f∘μ : NatMorphism N LiftN
  morph f∘μ = lift ∘ α
  comm-zero f∘μ i = lift (ζ i)
  comm-suc f∘μ i n = lift (σ n i)

  f∘μ≡id : f∘μ ≡ liftMorph
  f∘μ≡id = isContr→isProp (hinit LiftN) _ _

  open Helper (F .Fiber)

  P : ∀ n → α n ≡ n
  P n i = lower (f∘μ≡id i .morph n)
  -- Q-zero = ζ
  Q-suc : ∀ n → α (N .alg-suc n) ≡ N .alg-suc n
  Q-suc n = σ n □ apP (N .alg-suc) (P n)

  P-zero : P (N .alg-zero) ≡ ζ
  P-zero i j = hcomp (λ k → λ where
      (i = i0) → lower (f∘μ≡id j .comm-zero (~ k))
      (i = i1) → ζ (j ∨ ~ k)
      (j = i0) → ζ (~ k)
      (j = i1) → N .alg-zero
    ) (N .alg-zero)
  P-suc : ∀ n → P (N .alg-suc n) ≡ Q-suc n
  P-suc n i j = hcomp (λ k → λ where
      (i = i0) → lower (f∘μ≡id j .comm-suc (~ k) n)
      (i = i1) → compPath'-filler (σ n) (apP (N .alg-suc) (P n)) k j
      (j = i0) → σ n (~ k)
      (j = i1) → N .alg-suc n
    ) (N .alg-suc (P n j))

  Fsection : NatSection F
  section Fsection n = P n ! α-h n
  sec-comm-zero Fsection =
    P (N .alg-zero) ! α-h (N .alg-zero) ≡[ i ]⟨ P-zero i ! α-h _ ⟩
    ζ ! α-h (N .alg-zero)               ≡⟨ fromPathP ζ-h ⟩
    F .fib-zero                         ∎
  sec-comm-suc Fsection n =
    P (N .alg-suc n) ! α-h (N .alg-suc n)               ≡[ i ]⟨ P-suc n i ! α-h _ ⟩
    Q-suc n ! α-h (N .alg-suc n)                        ≡⟨ CompProperties.composite (σ n) _ ⟩
    apP (N .alg-suc) (P n) ! (σ n ! α-h (N .alg-suc n)) ≡[ i ]⟨ apP (N .alg-suc) (P n) ! fromPathP (σ-h n) i ⟩
    apP (N .alg-suc) (P n) ! (F .fib-suc (α-h n))       ≡⟨ SubstProperties.substDepends (N .alg-suc) (λ _ → F .fib-suc) ⟩
    F .fib-suc (P n ! α-h n)                            ∎

isNatInductive≡isNatHInitial : ∀ {ℓ'} {N : NatAlgebra ℓ'} ℓ → isNatInductive N (ℓ-max ℓ' ℓ) ≡ isNatHInitial N (ℓ-max ℓ' ℓ)
isNatInductive≡isNatHInitial {ℓ'} {N} ℓ = isoToPath (equivToIso (PropEquiv→Equiv isPropIsNatInductive isPropIsNatHInitial ind→init init→ind)) where
  open import Cubical.Foundations.Equiv
  open AlgebraPropositionality
  open AlgebraHInit→Ind N ℓ renaming (Fsection to init→ind)
  open AlgebraHInd→HInit renaming (isContrMorph to ind→init)

NatAlgebraℕ : NatAlgebra ℓ-zero
Carrier NatAlgebraℕ = ℕ
alg-zero NatAlgebraℕ = zero
alg-suc NatAlgebraℕ = suc

isNatInductiveℕ : ∀ {ℓ} → isNatInductive NatAlgebraℕ ℓ
section (isNatInductiveℕ F) = nat-sec where
  nat-sec : ∀ n → F .Fiber n
  nat-sec zero = F .fib-zero
  nat-sec (suc n) = F .fib-suc (nat-sec n)
sec-comm-zero (isNatInductiveℕ F) = refl
sec-comm-suc (isNatInductiveℕ F) n = refl

isNatHInitialℕ : ∀ {ℓ} → isNatHInitial NatAlgebraℕ ℓ
isNatHInitialℕ = transport (isNatInductive≡isNatHInitial _) isNatInductiveℕ
