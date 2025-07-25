{-
  TODO: upgrade to the default definition of CommAlgebra
-}
module Cubical.Algebra.Polynomials.TypevariateHIT.EquivUnivariateListPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra.AsModule
open import Cubical.Algebra.CommAlgebra.AsModule.FreeCommAlgebra
            renaming (inducedHomUnique to inducedHomUniqueHIT;
                      isIdByUMP to isIdByUMP-HIT)
open import Cubical.Algebra.Polynomials.UnivariateList.UniversalProperty
            renaming (generator to generatorList;
                      inducedHom to inducedHomList;
                      inducedHomUnique to inducedHomUniqueList;
                      isIdByUMP to isIdByUMP-List)

private variable
  ℓ : Level

module _ {R : CommRing ℓ} where
  open Theory renaming (inducedHom to inducedHomHIT)
  open CommRingStr ⦃...⦄
  private
    instance
      _ = snd R
    X-HIT = Construction.var {R = R} {I = Unit} tt
    X-List = generatorList R

  {-
    Construct an iso between the two versions of polynomials.
    Just using the universal properties to manually show that the two algebras are isomorphic
  -}
  private
    open AlgebraHoms
    open Iso
    to : CommAlgebraHom (R [ Unit ]) (ListPolyCommAlgebra R)
    to = inducedHomHIT (ListPolyCommAlgebra R) (λ _ → X-List)

    from : CommAlgebraHom (ListPolyCommAlgebra R) (R [ Unit ])
    from = inducedHomList R (CommAlgebra→Algebra (R [ Unit ])) X-HIT

    toPresX : fst to X-HIT ≡ X-List
    toPresX = refl

    fromPresX : fst from X-List ≡ X-HIT
    fromPresX = inducedMapGenerator R (CommAlgebra→Algebra (R [ Unit ])) X-HIT

    idList = AlgebraHoms.idAlgebraHom (CommAlgebra→Algebra (ListPolyCommAlgebra R))
    idHIT = AlgebraHoms.idAlgebraHom (CommAlgebra→Algebra (R [ Unit ]))

    toFrom : (x : ⟨ ListPolyCommAlgebra R ⟩) → fst to (fst from x) ≡ x
    toFrom = isIdByUMP-List R (to ∘a from) (cong (fst to) fromPresX)

    fromTo : (x : ⟨ R [ Unit ] ⟩) → fst from (fst to x) ≡ x
    fromTo = isIdByUMP-HIT (from ∘a to) λ {tt → fromPresX}

  typevariateListPolyIso : Iso ⟨ R [ Unit ] ⟩  ⟨ ListPolyCommAlgebra R ⟩
  fun typevariateListPolyIso = fst to
  inv typevariateListPolyIso = fst from
  rightInv typevariateListPolyIso = toFrom
  leftInv typevariateListPolyIso = fromTo

  typevariateListPolyEquiv : CommAlgebraEquiv (R [ Unit ]) (ListPolyCommAlgebra R)
  fst typevariateListPolyEquiv = isoToEquiv typevariateListPolyIso
  snd typevariateListPolyEquiv = snd to

  typevariateListPolyGenerator :
    fst (fst typevariateListPolyEquiv) X-HIT ≡ X-List
  typevariateListPolyGenerator = refl
