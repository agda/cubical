{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

module _ ((R , str) : CommRing ℓ) where

  initialCAlg : CommAlgebra (R , str) ℓ
  initialCAlg =
    let open CommRingStr str
    in  (R , commalgebrastr _ _ _ _ _ (λ r x → r · x)
                    (makeIsCommAlgebra (isSetRing (CommRing→Ring (R , str)))
                       +Assoc +Rid +Rinv +Comm
                       ·Assoc ·Lid
                       ·Ldist+ ·Comm
                        (λ x y z → sym (·Assoc x y z)) ·Ldist+ ·Rdist+ ·Lid
                         λ x y z → sym (·Assoc x y z)))


  module _ (A : CommAlgebra (R , str) ℓ) where
    open CommAlgebraStr ⦃... ⦄
    private
      instance
        _ : CommAlgebraStr (R , str) (fst A)
        _ = snd A
        _ : CommAlgebraStr (R , str) R
        _ = snd initialCAlg

    _*_ : R → (fst A) → (fst A)
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

    initialityIso : Iso (CommAlgebraHom initialCAlg A) (Unit* {ℓ = ℓ})
    initialityIso = iso (λ _ → tt*)
                        (λ _ → initialMap)
                        (λ {tt*x → refl})
                        λ f → sym (initialMapEq f)

    initialityPath : CommAlgebraHom initialCAlg A ≡ Unit*
    initialityPath = isoToPath initialityIso
