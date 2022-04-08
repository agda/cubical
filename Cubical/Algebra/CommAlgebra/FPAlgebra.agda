{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (f₁,⋯,fₘ) → R[X₁,⋯,Xₙ] → A → 0

  (where f₁,⋯,fₘ ∈ R[X₁,⋯,Xₙ])
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (inclOfFGIdeal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (inducedHom to freeInducedHom)
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Terminal
open import Cubical.Algebra.CommAlgebra.Kernel

open import Cubical.Algebra.Algebra.Properties


open import Cubical.Foundations.Structure

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} where
  open Construction using (var)
  Polynomials : (n : ℕ) → CommAlgebra R ℓ
  Polynomials n = R [ Fin n ]

  evPoly : {n : ℕ} (A : CommAlgebra R ℓ) → ⟨ Polynomials n ⟩ → FinVec ⟨ A ⟩ n → ⟨ A ⟩
  evPoly A P values = fst (freeInducedHom A values) P

  evPolyPoly : {n : ℕ} (P : ⟨ Polynomials n ⟩) → evPoly (Polynomials n) P var ≡ P
  evPolyPoly {n = n} P = cong (λ u → fst u P) (inducedHomVar R (Fin n))

  evPolyHomomorphic : {n : ℕ} (A B : CommAlgebra R ℓ) (f : CommAlgebraHom A B)
                     → (P : ⟨ Polynomials n ⟩) → (values : FinVec ⟨ A ⟩ n)
                     → (fst f) (evPoly A P values) ≡ evPoly B P (fst f ∘ values)
  evPolyHomomorphic A B f P values =
    (fst f) (evPoly A P values)                         ≡⟨ refl ⟩
    (fst f) (fst (freeInducedHom A values) P)           ≡⟨ refl ⟩
    fst (f ∘a freeInducedHom A values) P                ≡⟨ cong (λ u → fst u P) (natIndHomR f values) ⟩
    fst (freeInducedHom B (fst f ∘ values)) P           ≡⟨ refl ⟩
    evPoly B P (fst f ∘ values) ∎
    where open AlgebraHoms

  module _ {m : ℕ} (n : ℕ) (relation : FinVec ⟨ Polynomials n ⟩ m) where
    open CommAlgebraStr using (0a)
    open Cubical.Algebra.Algebra.Properties.AlgebraHoms

    relationsIdeal = generatedIdeal (Polynomials n) relation

    abstract
      {-
        The following definitions are abstract because of type checking speed
        problems - complete unfolding of FPAlgebra is triggered otherwise.
        This also means, the where blocks contain more type declarations than usual.
      -}
      FPAlgebra : CommAlgebra R ℓ
      FPAlgebra = Polynomials n / relationsIdeal

      modRelations : CommAlgebraHom (Polynomials n) (Polynomials n / relationsIdeal)
      modRelations = quotientMap (Polynomials n) relationsIdeal

      generator : (i : Fin n) → ⟨ FPAlgebra ⟩
      generator = fst modRelations ∘ var

      relationsHold : (i : Fin m) → evPoly FPAlgebra (relation i) generator ≡ 0a (snd FPAlgebra)
      relationsHold i =
        evPoly FPAlgebra (relation i) generator
        ≡⟨ sym (evPolyHomomorphic (Polynomials n) FPAlgebra modRelations (relation i) var) ⟩
        fst modRelations (evPoly (Polynomials n) (relation i) var)
        ≡⟨ cong (λ u → fst modRelations u) (evPolyPoly (relation i)) ⟩
        fst modRelations (relation i)
        ≡⟨ isZeroFromIdeal {R = R}
                           {A = (Polynomials n)}
                           {I = relationsIdeal}
                           (relation i)
                           (incInIdeal (Polynomials n) relation i ) ⟩
        0a (snd FPAlgebra) ∎
      inducedHom :
        {A : CommAlgebra R ℓ}
        (values : FinVec ⟨ A ⟩ n)
        (relationsHold : (i : Fin m) → evPoly A (relation i) values ≡ 0a (snd A))
        → CommAlgebraHom FPAlgebra A
      inducedHom {A = A} values relationsHold =
        quotientInducedHom
          (Polynomials n)
          relationsIdeal
          A
          freeHom
          isInKernel
        where
          freeHom : CommAlgebraHom (Polynomials n) A
          freeHom = freeInducedHom A values
          isInKernel :   fst (generatedIdeal (Polynomials n) relation)
                       ⊆ fst (kernel (Polynomials n) A freeHom)
          isInKernel = inclOfFGIdeal
                         (CommAlgebra→CommRing (Polynomials n))
                         relation
                         (kernel (Polynomials n) A freeHom)
                         relationsHold

      unique :
             {A : CommAlgebra R ℓ}
             (values : FinVec ⟨ A ⟩ n)
             (relationsHold : (i : Fin m) → evPoly A (relation i) values ≡ 0a (snd A))
             (f : CommAlgebraHom FPAlgebra A)
             → ((i : Fin n) → fst f (generator i) ≡ values i)
             → inducedHom {A = A} values relationsHold ≡ f
      unique {A = A} values relationsHold f hasCorrectValues =
        injectivePrecomp
          (Polynomials n)
          relationsIdeal
          A
          (inducedHom {A = A} values relationsHold)
          f
          (sym (
           f'     ≡⟨ sym (inv f') ⟩
           freeInducedHom A (evaluateAt A f')    ≡⟨ cong (freeInducedHom A) (funExt hasCorrectValues) ⟩
           freeInducedHom A values               ≡⟨ cong (freeInducedHom A) refl ⟩
           freeInducedHom A (evaluateAt A iHom') ≡⟨ inv iHom' ⟩
           iHom' ∎))
        where
          {-
                     Poly n
                      |    \
            modRelations    f'
                      ↓      ↘
                 FPAlgebra ─f→ A
          -}
          f' iHom' : CommAlgebraHom (Polynomials n) A
          f' = compAlgebraHom modRelations f
          iHom' = compAlgebraHom modRelations (inducedHom {A = A} values relationsHold)

          inv : retract (Iso.fun (homMapIso {I = Fin n} A)) (Iso.inv (homMapIso A))
          inv = Iso.leftInv (homMapIso {R = R} {I = Fin n} A)

  record FinitePresentation (A : CommAlgebra R ℓ) : Type ℓ where
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ m
      equiv : CommAlgebraEquiv (FPAlgebra n relations) A

  isFPAlgebra : (A : CommAlgebra R ℓ) → Type _
  isFPAlgebra A = ∥ FinitePresentation A ∥

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc

module Instances {R : CommRing ℓ} where
  open FinitePresentation

  {- Multivariate polynomials are finitely presented ... -}

  {- The initial R-algebra is finitely presented -}
  private
    R[⊥] : CommAlgebra R ℓ
    R[⊥] = Polynomials 0

    emptyGen : FinVec (fst R[⊥]) 0
    emptyGen = λ ()

    R[⊥]/⟨0⟩ : CommAlgebra R ℓ
    R[⊥]/⟨0⟩ = FPAlgebra 0 emptyGen

  contractibility : (B : CommAlgebra R ℓ)
                    → isContr (CommAlgebraHom R[⊥]/⟨0⟩ B)
  contractibility B = iHom , uniqueness
    where
      iHom : CommAlgebraHom R[⊥]/⟨0⟩ B
      iHom = inducedHom 0 emptyGen {A = B} (λ ()) (λ ())
      uniqueness : (f : CommAlgebraHom R[⊥]/⟨0⟩ B) →
                   iHom ≡ f
      uniqueness f = unique 0 emptyGen {A = B} (λ ()) (λ ()) f (λ ())

  initialCAlgFP : FinitePresentation (initialCAlg R)
  n initialCAlgFP = 0
  m initialCAlgFP = 0
  relations initialCAlgFP = emptyGen
  equiv initialCAlgFP =
    equivByInitiality R (FPAlgebra 0 emptyGen) contractibility

  {- The terminal R-algebra is finitely presented -}
  private
    unitGen : FinVec (fst R[⊥]) 1
    unitGen zero = 1a
      where open CommAlgebraStr (snd R[⊥])

    R[⊥]/⟨1⟩ : CommAlgebra R ℓ
    R[⊥]/⟨1⟩ = FPAlgebra 0 unitGen

  terminalCAlgFP : FinitePresentation (terminalCAlg R)
  n terminalCAlgFP = 0
  m terminalCAlgFP = 1
  relations terminalCAlgFP = unitGen
  equiv terminalCAlgFP = equivFrom1≡0 R R[⊥]/⟨1⟩ (sym (⋆-lid 1a) ∙ relationsHold 0 unitGen zero)
    where open CommAlgebraStr (snd R[⊥]/⟨1⟩)
