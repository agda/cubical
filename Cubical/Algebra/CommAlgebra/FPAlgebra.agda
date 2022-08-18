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
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Unit
  renaming (UnitCommAlgebra to TerminalCAlg)
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.Algebra.Properties
open import Cubical.Algebra.Algebra


private
  variable
    ℓ ℓ' : Level

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
      modRelations = quotientHom (Polynomials n) relationsIdeal

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

      module _
        (A : CommAlgebra R ℓ)
        (values : FinVec ⟨ A ⟩ n)
        (relationsHold : (i : Fin m) → evPoly A (relation i) values ≡ 0a (snd A))
        where abstract
        {-
          We repeat the abstract keyword here because the contents of a child module are not
          covered by the outer abstract keyword. This behaves like a single big abstract
          block as long as the child module is anonymous.
        -}

        private
          freeHom : CommAlgebraHom (Polynomials n) A
          freeHom = freeInducedHom A values

          isInKernel :   fst (generatedIdeal (Polynomials n) relation)
                       ⊆ fst (kernel (Polynomials n) A freeHom)
          isInKernel = inclOfFGIdeal
                         (CommAlgebra→CommRing (Polynomials n))
                         relation
                         (kernel (Polynomials n) A freeHom)
                         relationsHold

        inducedHom : CommAlgebraHom FPAlgebra A
        inducedHom =
          quotientInducedHom
            (Polynomials n)
            relationsIdeal
            A
            freeHom
            isInKernel

        inducedHomOnGenerators :
          (i : Fin n)
          → fst inducedHom (generator i) ≡ values i
        inducedHomOnGenerators i =
          cong (λ f → fst f (var i))
          (inducedHom∘quotientHom (Polynomials n) relationsIdeal A freeHom isInKernel)

        unique :
             (f : CommAlgebraHom FPAlgebra A)
             → ((i : Fin n) → fst f (generator i) ≡ values i)
             → inducedHom ≡ f
        unique f hasCorrectValues =
          injectivePrecomp
            (Polynomials n)
            relationsIdeal
            A
            inducedHom
            f
            (sym (
             f'                                    ≡⟨ sym (inv f') ⟩
             freeInducedHom A (evaluateAt A f')    ≡⟨ cong (freeInducedHom A)
                                                           (funExt hasCorrectValues) ⟩
             freeInducedHom A values               ≡⟨ cong (freeInducedHom A)
                                                           (sym (funExt inducedHomOnGenerators)) ⟩
             freeInducedHom A (evaluateAt A iHom') ≡⟨ inv iHom' ⟩
             iHom'                                 ∎))
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
            iHom' = compAlgebraHom modRelations inducedHom

            inv : retract (Iso.fun (homMapIso {I = Fin n} A)) (Iso.inv (homMapIso A))
            inv = Iso.leftInv (homMapIso {R = R} {I = Fin n} A)

        universal :
          isContr (Σ[ f ∈ CommAlgebraHom FPAlgebra A ] ((i : Fin n) → fst f (generator i) ≡ values i))
        universal =
          (inducedHom , inducedHomOnGenerators)
          , λ {(f , mapsValues)
              → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetCommAlgebra A _ _))
                       (unique f mapsValues)}

      {- ∀ A : Comm-R-Algebra,
         ∀ J : Finitely-generated-Ideal,
         Hom(R[I]/J,A) is isomorphic to the Set of roots of the generators of J
      -}

      zeroLocus : (A : CommAlgebra R ℓ) → Type ℓ
      zeroLocus A = Σ[ v ∈ FinVec ⟨ A ⟩ n ] ((i : Fin m) → evPoly A (relation i) v ≡ 0a (snd A))

      inducedHomFP : (A : CommAlgebra R ℓ) →
                      zeroLocus A → CommAlgebraHom FPAlgebra A
      inducedHomFP A d = inducedHom A (fst d) (snd d)

      evaluateAtFP : {A : CommAlgebra R ℓ} →
                      CommAlgebraHom FPAlgebra A → zeroLocus A
      evaluateAtFP {A} f = value ,
        λ i →  evPoly A (relation i) value                            ≡⟨ step1 (relation i) ⟩
            fst compHom (evPoly (Polynomials n) (relation i) var)  ≡⟨ refl ⟩
            (fst f) ((fst modRelations)
                       (evPoly (Polynomials n) (relation i) var))  ≡⟨ cong
                                                                       (fst f)
                                                                       (evPolyHomomorphic
                                                                         (Polynomials n)
                                                                         FPAlgebra
                                                                         modRelations
                                                                         (relation i) var) ⟩
            (fst f) (evPoly FPAlgebra (relation i) generator)      ≡⟨ cong (fst f) (relationsHold i) ⟩
            (fst f) (0a (snd FPAlgebra))                           ≡⟨ IsAlgebraHom.pres0 (snd f) ⟩
            0a (snd A) ∎
        where
          compHom : CommAlgebraHom (Polynomials n) A
          compHom = CommAlgebraHoms.compCommAlgebraHom (Polynomials n) FPAlgebra A modRelations f
          value : FinVec ⟨ A ⟩ n
          value = (Iso.fun (homMapIso A)) compHom
          step1 : (x : ⟨ Polynomials n ⟩) → evPoly A x value ≡ fst compHom (evPoly (Polynomials n) x var)
          step1 x = sym (evPolyHomomorphic (Polynomials n) A compHom x var)

      FPHomIso : {A : CommAlgebra R ℓ} →
                  Iso (CommAlgebraHom FPAlgebra A) (zeroLocus A)
      Iso.fun FPHomIso = evaluateAtFP
      Iso.inv FPHomIso = inducedHomFP _
      Iso.rightInv (FPHomIso {A}) =
        λ b → Σ≡Prop
                (λ x → isPropΠ
                  (λ i → isSetCommAlgebra A
                          (evPoly A (relation i) x)
                          (0a (snd A))))
                (funExt (inducedHomOnGenerators A (fst b) (snd b)))
      Iso.leftInv (FPHomIso {A}) =
        λ a → Σ≡Prop (λ f → isPropIsCommAlgebraHom {ℓ} {R} {ℓ} {ℓ} {FPAlgebra} {A} f)
                 λ i → fst (unique A
                             (fst (evaluateAtFP {A} a))
                             (snd (evaluateAtFP a))
                             a
                             (λ j → refl)
                             i)

      homMapPathFP : (A : CommAlgebra R ℓ)→ CommAlgebraHom FPAlgebra A ≡ zeroLocus A
      homMapPathFP A = isoToPath (FPHomIso {A})

      isSetZeroLocus : (A : CommAlgebra R ℓ) → isSet (zeroLocus A)
      isSetZeroLocus A =  J (λ y _ → isSet y)
                       (isSetAlgebraHom (CommAlgebra→Algebra FPAlgebra) (CommAlgebra→Algebra A))
                       (homMapPathFP A)

  record FinitePresentation (A : CommAlgebra R ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ m
      equiv : CommAlgebraEquiv (FPAlgebra n relations) A

  isFPAlgebra : (A : CommAlgebra R ℓ') → Type _
  isFPAlgebra A = ∥ FinitePresentation A ∥₁

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc

module Instances (R : CommRing ℓ) where
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
