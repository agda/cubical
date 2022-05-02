{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra

private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where

  initialCAlg : CommAlgebra R ℓ
  initialCAlg =
    let open CommRingStr (snd R)
    in  (fst R , commalgebrastr _ _ _ _ _ (λ r x → r · x)
                    (makeIsCommAlgebra (isSetRing (CommRing→Ring R))
                       +Assoc +Rid +Rinv +Comm
                       ·Assoc ·Lid
                       ·Ldist+ ·Comm
                        (λ x y z → sym (·Assoc x y z)) ·Ldist+ ·Rdist+ ·Lid
                         λ x y z → sym (·Assoc x y z)))

  module _ (A : CommAlgebra R ℓ) where
    open CommAlgebraStr ⦃... ⦄
    private
      instance
        _ : CommAlgebraStr R (fst A)
        _ = snd A
        _ : CommAlgebraStr R (fst R)
        _ = snd initialCAlg

    _*_ : fst R → (fst A) → (fst A)
    r * a = CommAlgebraStr._⋆_ (snd A) r a

    initialMap : CommAlgebraHom initialCAlg A
    initialMap =
      makeCommAlgebraHom {M = initialCAlg} {N = A}
        (λ r → r * 1a)
        (⋆-lid _)
        (λ x y → ⋆-ldist x y 1a)
        (λ x y →  (x · y) * 1a ≡⟨ ⋆-assoc _ _ _ ⟩
                           x * (y * 1a)                   ≡[ i ]⟨ x * (·Lid (y * 1a) (~ i)) ⟩
                           x * (1a · (y * 1a))            ≡⟨ sym (⋆-lassoc _ _ _) ⟩
                           (x * 1a) · (y * 1a) ∎)
        (λ r x → (r · x) * 1a   ≡⟨ ⋆-assoc _ _ _ ⟩
                         (r * (x * 1a)) ∎)

    initialMapEq : (f : CommAlgebraHom initialCAlg A)
                   → f ≡ initialMap
    initialMapEq f =
      let open IsAlgebraHom (snd f)
      in Σ≡Prop
           (isPropIsCommAlgebraHom {M = initialCAlg} {N = A})
             λ i x →
               ((fst f) x                              ≡⟨ cong (fst f) (sym (·Rid _)) ⟩
               fst f (x · 1a)                          ≡⟨ pres⋆ x 1a ⟩
               CommAlgebraStr._⋆_ (snd A) x (fst f 1a) ≡⟨ cong
                                                           (λ u → (snd A CommAlgebraStr.⋆ x) u)
                                                           pres1 ⟩
               (CommAlgebraStr._⋆_ (snd A) x 1a) ∎) i

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
        open CommAlgebraHoms
        to : CommAlgebraHom A initialCAlg
        to = fst (isInitial initialCAlg)

        from : CommAlgebraHom initialCAlg A
        from = initialMap A

        asIso : Iso (fst A) (fst initialCAlg)
        Iso.fun asIso = fst to
        Iso.inv asIso = fst from
        Iso.rightInv asIso =
          λ x i → cong
                    fst
                    (isContr→isProp (initialityContr initialCAlg) (compCommAlgebraHom initialCAlg A initialCAlg from to ) (idCommAlgebraHom initialCAlg))
                    i x
        Iso.leftInv asIso =
          λ x i → cong
                    fst
                    (isContr→isProp (isInitial A) (compCommAlgebraHom A initialCAlg A to from) (idCommAlgebraHom A))
                    i x
