{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Instances.Initial where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

module CommAlgebraExamples ((R , str) : CommRing ℓ) where

  initial : CommAlgebra (R , str) ℓ
  initial =
    let open CommRingStr str
    in  (R , commalgebrastr _ _ _ _ _ (λ r x → r · x)
                    (makeIsCommAlgebra (isSetRing (CommRing→Ring (R , str)))
                       +Assoc +Rid +Rinv +Comm
                       ·Assoc ·Lid
                       ·Ldist+ ·-comm
                        (λ x y z → sym (·Assoc x y z)) ·Ldist+ ·Rdist+ ·Lid
                         λ x y z → sym (·Assoc x y z)))


  module _ (A : CommAlgebra (R , str) ℓ) where
    open CommAlgebraStr ⦃... ⦄
    instance
      _ : CommAlgebraStr (R , str) (fst A)
      _ = snd A
      _ : CommAlgebraStr (R , str) R
      _ = snd initial

    _*_ : R → (fst A) → (fst A)
    r * a = CommAlgebraStr._⋆_ (snd A) r a

    initialMap : CommAlgebraHom initial A
    initialMap =
      makeCommAlgebraHom {M = initial} {N = A}
        (λ r → r * 1a)
        (⋆-lid _)
        (λ x y → ⋆-ldist x y 1a)
        (λ x y →  (x · y) * 1a ≡⟨ ⋆-assoc _ _ _ ⟩
                           x * (y * 1a)                   ≡[ i ]⟨ x * (·Lid (y * 1a) (~ i)) ⟩
                           x * (1a · (y * 1a))            ≡⟨ sym (⋆-lassoc _ _ _) ⟩
                           (x * 1a) · (y * 1a) ∎)
        (λ r x → (r · x) * 1a   ≡⟨ ⋆-assoc _ _ _ ⟩
                         (r * (x * 1a)) ∎)

    initialMapEq : (f : CommAlgebraHom initial A)
                   → f ≡ initialMap
    initialMapEq f =
      let open IsAlgebraHom (snd f)
      in Σ≡Prop
           (isPropIsCommAlgebraHom {M = initial} {N = A})
             λ i x →
               ((fst f) x                              ≡⟨ cong (fst f) (sym (·Rid _)) ⟩
               fst f (x · 1a)                          ≡⟨ pres⋆ x 1a ⟩
               CommAlgebraStr._⋆_ (snd A) x (fst f 1a) ≡⟨ cong
                                                           (λ u → (snd A CommAlgebraStr.⋆ x) u)
                                                           pres1 ⟩
               (CommAlgebraStr._⋆_ (snd A) x 1a) ∎) i

    isInitial : CommAlgebraHom initial A ≡ Unit*
    isInitial =
      isoToPath (iso (λ _ → tt*)
                     (λ _ → initialMap)
                     (λ {tt*x → refl})
                     λ f → sym (initialMapEq f))
