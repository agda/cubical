{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.Instances.Polynomials where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebraAlt.Base
open import Cubical.Algebra.CommRing.Instances.Polynomials.Typevariate

private
  variable
    ℓ ℓ' : Level

_[_] : (R : CommRing ℓ) (I : Type ℓ') → CommAlgebra R _
R [ I ] = (R [ I ]ᵣ) , constPolynomial R I


{-
evaluateAt : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'')
             (f : CommAlgebraHom (R [ I ]) A)
             → (I → fst A)
evaluateAt A f x = f $a (Construction.var x)

inducedHom : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'')
             (φ : I → fst A )
             → CommAlgebraHom (R [ I ]) A
inducedHom A φ = Theory.inducedHom A φ


homMapIso : {R : CommRing ℓ} {I : Type ℓ''} (A : CommAlgebra R ℓ')
             → Iso (CommAlgebraHom (R [ I ]) A) (I → (fst A))
Iso.fun (homMapIso A) = evaluateAt A
Iso.inv (homMapIso A) = inducedHom A
Iso.rightInv (homMapIso A) = λ ϕ → Theory.mapRetrievable A ϕ
Iso.leftInv (homMapIso {R = R} {I = I} A) =
  λ f → Σ≡Prop (λ f → isPropIsCommAlgebraHom {M = R [ I ]} {N = A} f)
               (Theory.homRetrievable A f)

inducedHomUnique :
  {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'') (φ : I → fst A )
  → (f : CommAlgebraHom (R [ I ]) A) → ((i : I) → fst f (Construction.var i) ≡ φ i)
  → f ≡ inducedHom A φ
inducedHomUnique {I = I} A φ f p =
  isoFunInjective (homMapIso A) f (inducedHom A φ) λ j i → p i j

homMapPath : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R (ℓ-max ℓ ℓ'))
             → CommAlgebraHom (R [ I ]) A ≡ (I → fst A)
homMapPath A = isoToPath (homMapIso A)

{- Corollary: Two homomorphisms with the same values on generators are equal -}
equalByUMP : {R : CommRing ℓ} {I : Type ℓ'}
           → (A : CommAlgebra R ℓ'')
           → (f g : CommAlgebraHom (R [ I ]) A)
           → ((i : I) → fst f (Construction.var i) ≡ fst g (Construction.var i))
           → (x : ⟨ R [ I ] ⟩) → fst f x ≡ fst g x
equalByUMP {R = R} {I = I} A f g = funExt⁻ ∘ cong fst ∘ isoFunInjective (homMapIso A) f g ∘ funExt

{- A corollary, which is useful for constructing isomorphisms to
   algebras with the same universal property -}
isIdByUMP : {R : CommRing ℓ} {I : Type ℓ'}
          → (f : CommAlgebraHom (R [ I ]) (R [ I ]))
          → ((i : I) → fst f (Construction.var i) ≡ Construction.var i)
          → (x : ⟨ R [ I ] ⟩) → fst f x ≡ x
isIdByUMP {R = R} {I = I} f p = equalByUMP (R [ I ]) f (idCAlgHom (R [ I ])) p

-- The homomorphism induced by the variables is the identity.
inducedHomVar : (R : CommRing ℓ) (I : Type ℓ')
              → inducedHom (R [ I ]) Construction.var ≡ idCAlgHom (R [ I ])
inducedHomVar R I = isoFunInjective (homMapIso (R [ I ])) _ _ refl

module _ {R : CommRing ℓ} {A B : CommAlgebra R ℓ''} where
  open AlgebraHoms
  A′ = CommAlgebra→Algebra A
  B′ = CommAlgebra→Algebra B
  R′ = (CommRing→Ring R)
  ν : AlgebraHom A′ B′ → (⟨ A ⟩ → ⟨ B ⟩)
  ν φ = φ .fst

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓ψ
    Hom(R[I],B) → (I → B)
  -}
  naturalEvR : {I : Type ℓ'} (ψ : CommAlgebraHom A B)
             (f : CommAlgebraHom (R [ I ]) A)
             → (fst ψ) ∘ evaluateAt A f ≡ evaluateAt B (ψ ∘a f)
  naturalEvR ψ f = refl

  {-
    Hom(R[I],A) ← (I → A)
         ↓          ↓ψ
    Hom(R[I],B) ← (I → B)
  -}
  natIndHomR : {I : Type ℓ'} (ψ : CommAlgebraHom A B)
               (ϕ : I → ⟨ A ⟩)
               → ψ ∘a inducedHom A ϕ ≡ inducedHom B (fst ψ ∘ ϕ)
  natIndHomR ψ ϕ = isoFunInjective (homMapIso B) _ _
                (evaluateAt B (ψ ∘a (inducedHom A ϕ))        ≡⟨ refl ⟩
                 fst ψ ∘ evaluateAt A (inducedHom A ϕ)       ≡⟨ refl ⟩
                 fst ψ ∘ ϕ                                   ≡⟨ Iso.rightInv (homMapIso B) _ ⟩
                 evaluateAt B (inducedHom B (fst ψ ∘ ϕ))     ∎)

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓
    Hom(R[J],A) → (J → A)
  -}
  naturalEvL : {I J : Type ℓ'} (φ : J → I)
             (f : CommAlgebraHom (R [ I ]) A)
             → (evaluateAt A f) ∘ φ
               ≡ evaluateAt A (f ∘a (inducedHom (R [ I ]) (λ x → Construction.var (φ x))))
  naturalEvL φ f = refl

module _ {R : CommRing ℓ} where
  {-
    Prove that the FreeCommAlgebra over R on zero generators is
    isomorphic to the initial R-Algebra - R itsself.
  -}
  freeOn⊥ : CommAlgebraEquiv (R [ ⊥ ]) (initialCAlg R)
  freeOn⊥ =
     equivByInitiality
        R (R [ ⊥ ])
          {- Show that R[⊥] has the universal property of the
             initial R-Algbera and conclude that those are isomorphic -}
        λ B →  let to : CommAlgebraHom (R [ ⊥ ]) B → (⊥ → fst B)
                   to = evaluateAt B

                   from :  (⊥ → fst B) → CommAlgebraHom (R [ ⊥ ]) B
                   from = inducedHom B

                   from-to : (x : _) → from (to x) ≡ x
                   from-to x =
                     Σ≡Prop (λ f → isPropIsCommAlgebraHom {M = R [ ⊥ ]} {N = B} f)
                            (Theory.homRetrievable B x)

                   equiv : CommAlgebraHom (R [ ⊥ ]) B ≃ (⊥ → fst B)
                   equiv =
                     isoToEquiv
                       (iso to from (λ x → isContr→isOfHLevel 1 isContr⊥→A _ _) from-to)
               in isOfHLevelRespectEquiv 0 (invEquiv equiv) isContr⊥→A
-}
