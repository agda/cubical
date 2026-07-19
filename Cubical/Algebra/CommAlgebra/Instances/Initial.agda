module Cubical.Algebra.CommAlgebra.Instances.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_$_)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Algebra.Algebra.Properties
open import Cubical.Algebra.CommAlgebra
import Cubical.Algebra.Algebra.Properties

open AlgebraHoms

private variable
  ℓ : Level

module _ (R : CommRing ℓ) where
  module _ where
    open CommRingStr (snd R)

    initialCAlg : CommAlgebra R ℓ
    initialCAlg .fst = R
    initialCAlg .snd = idCommRingHom R

  module _ (A : CommAlgebra R ℓ) where
--    open CommAlgebraStr ⦃... ⦄

    initialMap : CommAlgebraHom initialCAlg A
    initialMap = CommRingHom→CommAlgebraHom (A .snd) (CommRingHom≡ refl)

    initialMapEq : (f : CommAlgebraHom initialCAlg A)
                   → f ≡ initialMap
    initialMapEq f = CommAlgebraHom≡ $
                     funExt $
                     λ r → f $ca r          ≡⟨ (cong (λ h → h .fst r) $ f .snd .IsCommAlgebraHom.commutes) ⟩
                           initialMap $ca r ∎

    initialMapProp : (f g : CommAlgebraHom initialCAlg A)
                     → f ≡ g
    initialMapProp f g = initialMapEq f ∙ sym (initialMapEq g)


    initialityIso : Iso (CommAlgebraHom initialCAlg A) (Unit* {ℓ = ℓ})
    initialityIso = iso (λ _ → tt*)
                        (λ _ → initialMap)
                        (λ {tt*x → refl})
                        λ f → sym (initialMapEq f)

    initialityPath : CommAlgebraHom initialCAlg A ≡ Unit*
    initialityPath = isoToPath initialityIso

    initialityContr : isContr (CommAlgebraHom initialCAlg A)
    initialityContr = initialMap , λ ϕ → sym (initialMapEq ϕ)


  {-
    Show that any R-Algebra with the same universal property
    as the initial R-Algebra, is isomorphic to the initial
    R-Algebra.
  -}
  module _ (A : CommAlgebra R ℓ) where
    equivByInitiality :
      (isInitial : (B : CommAlgebra R ℓ) → isContr (CommAlgebraHom A B))
      → CommAlgebraEquiv A (initialCAlg)
    equivByInitiality isInitial = isoToEquiv asIso , snd to
      where
        -- open CommAlgebraHoms
        to : CommAlgebraHom A initialCAlg
        to = fst (isInitial initialCAlg)

        from : CommAlgebraHom initialCAlg A
        from = initialMap A

        asIso : Iso ⟨ A ⟩ₐ ⟨ initialCAlg ⟩ₐ
        Iso.fun asIso = fst to
        Iso.inv asIso = fst from
        Iso.rightInv asIso =
          λ x i → cong
                    fst
                    (isContr→isProp (initialityContr initialCAlg) (to ∘ca from) (idCAlgHom initialCAlg))
                    i x
        Iso.leftInv asIso =
          λ x i → cong
                    fst
                    (isContr→isProp (isInitial A) (from ∘ca to) (idCAlgHom A))
                    i x
