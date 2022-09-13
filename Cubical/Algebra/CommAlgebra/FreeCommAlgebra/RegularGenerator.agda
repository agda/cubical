{-
  The generator 'X' of the algebra of univariate polynomials is a regular element,
  i.e. the multiplication map 'X ·_' is injective (we will actually show it is an Embedding)
-}
{-# OPTIONS --safe #-}

module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.RegularGenerator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding

open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (generator to generatorHIT)
open import Cubical.Algebra.CommAlgebra.UnivariatePolyList
open import Cubical.Algebra.Polynomials.TypevariateHIT.EquivUnivariateListPoly
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

private variable
    ℓ : Level

{-
  We start by constructing a commutative square:
  (L=List, H=HIT)

    R[X]-L ←─ R[X]-H
     ∣         ∣
     X·         X·
     ↓          ↓
    R[X]-L ─→ R[X]-H

  which will allow us to expose the right X· as a
  composition of embeddings
-}
module _ {R : CommRing ℓ} where
  open AlgebraHoms
  open PolyModTheory R using (prod-Xn; X*Poly)
  open CommAlgebraStr ⦃...⦄
  private
    instance _ = snd (R [ Unit ])
             _ = snd (ListPolyCommAlgebra R)

    HIT→List : CommAlgebraEquiv (R [ Unit ]) (ListPolyCommAlgebra R)
    HIT→List = typevariateListPolyEquiv

    List→HIT : CommAlgebraEquiv (ListPolyCommAlgebra R) (R [ Unit ])
    List→HIT = typevariateListPolyEquivInv

    open IsAlgebraHom (snd List→HIT)

    X : ⟨ R [ Unit ] ⟩
    X = generatorHIT tt

    X-List = generator R

    commutes : (p : ⟨ R [ Unit ] ⟩) → fst (fst List→HIT) (prod-Xn 1 (fst (fst HIT→List) p)) ≡ X · p
    commutes p =
      fst (fst List→HIT) (prod-Xn 1 (fst (fst HIT→List) p))                 ≡⟨ cong (fst (fst List→HIT)) (sym (X*Poly (fst (fst HIT→List) p))) ⟩
      fst (fst List→HIT) (X-List · (fst (fst HIT→List) p))                  ≡⟨ pres· X-List (fst (fst HIT→List) p) ⟩
      fst (fst List→HIT) X-List · fst (fst List→HIT) (fst (fst HIT→List) p) ≡[ i ]⟨ typevariateListPolyInvGenerator i · fst (fst List→HIT) (fst (fst HIT→List) p) ⟩
      X · fst (fst List→HIT) (fst (fst HIT→List) p)                         ≡[ i ]⟨ X · (Iso.leftInv typevariateListPolyIso p i ) ⟩
      X · p ∎

  prod-X-isEmbedding : isEmbedding (X ·_)
  prod-X-isEmbedding =
    subst isEmbedding
          (λ i p → commutes p i)
          (isEmbedding-∘ {f = (fst (fst List→HIT))}
            (isEquiv→isEmbedding (snd (fst List→HIT)))
            (isEmbedding-∘ {f = prod-Xn 1} {h = fst (fst HIT→List)}
              (prod-X-embedding R)
              (isEquiv→isEmbedding (snd (fst HIT→List)))))
