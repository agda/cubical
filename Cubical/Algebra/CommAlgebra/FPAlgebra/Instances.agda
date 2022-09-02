{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (inclOfFGIdeal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
  renaming (inducedHom to freeInducedHom)
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal using (IdealsIn)
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Unit
  renaming (UnitCommAlgebra to TerminalCAlg)
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.Algebra

open import Cubical.Algebra.CommAlgebra.FPAlgebra.Base

private
  variable
    ℓ ℓ' : Level


module _ (R : CommRing ℓ) where
  open FinitePresentation

  {- Every (multivariate) polynomial algebra is finitely presented -}
  module _ (n : ℕ) where
    private
      A : CommAlgebra R ℓ
      A = Polynomials n

      emptyGen : FinVec (fst A) 0
      emptyGen = λ ()

      B : CommAlgebra R ℓ
      B = FPAlgebra n emptyGen

    polynomialAlgFP : FinitePresentation A
    FinitePresentation.n polynomialAlgFP = n
    m polynomialAlgFP = 0
    relations polynomialAlgFP = emptyGen
    equiv polynomialAlgFP =
      -- Idea: A and B enjoy the same universal property.
      toAAsEquiv , snd toA
      where
        toA : CommAlgebraHom B A
        toA = inducedHom n emptyGen A Construction.var (λ ())
        fromA : CommAlgebraHom A B
        fromA = freeInducedHom B (generator _ _)
        open AlgebraHoms
        inverse1 : fromA ∘a toA ≡ idAlgebraHom _
        inverse1 =
          fromA ∘a toA
            ≡⟨ sym (unique _ _ _ _ _ _ (λ i → cong (fst fromA) (
                 fst toA (generator n emptyGen i)
                   ≡⟨ inducedHomOnGenerators _ _ _ _ _ _ ⟩
                 Construction.var i
                   ∎))) ⟩
          inducedHom n emptyGen B (generator _ _) (relationsHold _ _)
            ≡⟨ unique _ _ _ _ _ _ (λ i → refl) ⟩
          idAlgebraHom _
            ∎
        inverse2 : toA ∘a fromA ≡ idAlgebraHom _
        inverse2 = isoFunInjective (homMapIso A) _ _ (
          evaluateAt A (toA ∘a fromA)   ≡⟨ sym (naturalEvR {A = B} {B = A} toA fromA) ⟩
          fst toA ∘ evaluateAt B fromA  ≡⟨ refl ⟩
          fst toA ∘ generator _ _       ≡⟨ funExt (inducedHomOnGenerators _ _ _ _ _)⟩
          Construction.var              ∎)
        toAAsEquiv : ⟨ B ⟩ ≃ ⟨ A ⟩
        toAAsEquiv = isoToEquiv (iso (fst toA)
                                     (fst fromA)
                                     (λ a i → fst (inverse2 i) a)
                                     (λ b i → fst (inverse1 i) b))

  {- The initial R-algebra is finitely presented -}
  private
    R[⊥] : CommAlgebra R ℓ
    R[⊥] = Polynomials 0

    emptyGen : FinVec (fst R[⊥]) 0
    emptyGen = λ ()

    R[⊥]/⟨0⟩ : CommAlgebra R ℓ
    R[⊥]/⟨0⟩ = FPAlgebra 0 emptyGen

  R[⊥]/⟨0⟩IsInitial : (B : CommAlgebra R ℓ)
                     → isContr (CommAlgebraHom R[⊥]/⟨0⟩ B)
  R[⊥]/⟨0⟩IsInitial B = iHom , uniqueness
    where
      iHom : CommAlgebraHom R[⊥]/⟨0⟩ B
      iHom = inducedHom 0 emptyGen B (λ ()) (λ ())
      uniqueness : (f : CommAlgebraHom R[⊥]/⟨0⟩ B) →
                   iHom ≡ f
      uniqueness f = unique 0 emptyGen B (λ ()) (λ ()) f (λ ())

  initialCAlgFP : FinitePresentation (initialCAlg R)
  n initialCAlgFP = 0
  m initialCAlgFP = 0
  relations initialCAlgFP = emptyGen
  equiv initialCAlgFP =
    equivByInitiality R R[⊥]/⟨0⟩ R[⊥]/⟨0⟩IsInitial

  {- The terminal R-algebra is finitely presented -}
  private
    unitGen : FinVec (fst R[⊥]) 1
    unitGen zero = 1a
      where open CommAlgebraStr (snd R[⊥])

    R[⊥]/⟨1⟩ : CommAlgebra R ℓ
    R[⊥]/⟨1⟩ = FPAlgebra 0 unitGen

  terminalCAlgFP : FinitePresentation (TerminalCAlg R)
  n terminalCAlgFP = 0
  m terminalCAlgFP = 1
  relations terminalCAlgFP = unitGen
  equiv terminalCAlgFP = equivFrom1≡0 R R[⊥]/⟨1⟩ (sym (⋆IdL 1a) ∙ relationsHold 0 unitGen zero)
    where open CommAlgebraStr (snd R[⊥]/⟨1⟩)


  {-
    Quotients of the base ring by finitely generated ideals are finitely presented.
  -}
  module _ {m : ℕ} (xs : FinVec ⟨ R ⟩ m) where
    ⟨xs⟩ : IdealsIn (initialCAlg R)
    ⟨xs⟩ = generatedIdeal (initialCAlg R) xs

    R/⟨xs⟩ = (initialCAlg R) / ⟨xs⟩

    open CommAlgebraStr ⦃...⦄
    private
      rels : FinVec ⟨ Polynomials {R = R} 0 ⟩ m
      rels = Construction.const ∘ xs

      B = FPAlgebra 0 rels

      π = quotientHom (initialCAlg R) ⟨xs⟩
      instance
        _ = snd R/⟨xs⟩
        _ = snd (initialCAlg R)
        _ = snd B

      πxs≡0 : (i : Fin m) → π $a xs i ≡ 0a
      πxs≡0 i = isZeroFromIdeal {A = initialCAlg R} {I = ⟨xs⟩} (xs i)
               (incInIdeal (initialCAlg R) xs i)



    R/⟨xs⟩FP : FinitePresentation R/⟨xs⟩
    n R/⟨xs⟩FP = 0
    FinitePresentation.m R/⟨xs⟩FP = m
    relations R/⟨xs⟩FP = rels
    equiv R/⟨xs⟩FP = (isoToEquiv (iso (fst toA) (fst fromA)
                                    (λ a i → toFrom i $a a)
                                    λ a i → fromTo i $a a))
                   , (snd toA)
      where
        toA : CommAlgebraHom B R/⟨xs⟩
        toA = inducedHom 0 rels R/⟨xs⟩ (λ ()) relation-holds
          where
            vals : FinVec ⟨ R/⟨xs⟩ ⟩ 0
            vals ()
            vals' : FinVec ⟨ initialCAlg R ⟩ 0
            vals' ()
            relation-holds =  λ i →
               evPoly R/⟨xs⟩ (rels i) vals    ≡⟨ sym
                                                (evPolyHomomorphic
                                                  (initialCAlg R)
                                                     R/⟨xs⟩
                                                     π
                                                     (rels i)
                                                     vals') ⟩
              π $a (evPoly (initialCAlg R)
                           (rels i)
                           vals')             ≡⟨ cong (π $a_) (·IdR (xs i)) ⟩
              π $a xs i                       ≡⟨ πxs≡0 i ⟩
              0a                              ∎
        {-
            R ─→   R/⟨xs⟩
          id↓       ↓ ∃!
            R ─→   R[⊥]/⟨rels⟩
        -}

        fromA : CommAlgebraHom R/⟨xs⟩ B
        fromA =
          quotientInducedHom
            (initialCAlg R)
            ⟨xs⟩
            B
            (initialMap R B)
            (inclOfFGIdeal
              (CommAlgebra→CommRing (initialCAlg R))
              xs
              (kernel (initialCAlg R) B (initialMap R B))
              (relationsHold 0 rels))

        open AlgebraHoms

        fromTo : fromA ∘a toA ≡ idCAlgHom B
        fromTo = cong fst
          (isContr→isProp (universal 0 rels B (λ ()) (relationsHold 0 rels))
                          (fromA ∘a toA , (λ ()))
                          (idCAlgHom B , (λ ())))

        toFrom : toA ∘a fromA ≡ idCAlgHom R/⟨xs⟩
        toFrom = injectivePrecomp (initialCAlg R) ⟨xs⟩ R/⟨xs⟩ (toA ∘a fromA) (idCAlgHom R/⟨xs⟩)
                   (isContr→isProp (initialityContr R R/⟨xs⟩) _ _)

  module _ {m : ℕ} (x : ⟨ R ⟩) where
    R/⟨x⟩FP : FinitePresentation (initialCAlg R / generatedIdeal (initialCAlg R) (replicateFinVec 1 x))
    R/⟨x⟩FP = R/⟨xs⟩FP (replicateFinVec 1 x)
