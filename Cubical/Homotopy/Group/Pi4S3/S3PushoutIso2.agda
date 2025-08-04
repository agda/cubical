{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2 where

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.HITs.S2

≡→Pushout⋁↪fold⋁≡ : ∀ {ℓ} {A B : Pointed ℓ}
  → (A ≡ B) → Pushout⋁↪fold⋁∙ A ≡ Pushout⋁↪fold⋁∙ B
≡→Pushout⋁↪fold⋁≡ = cong Pushout⋁↪fold⋁∙

private
  ∙≃→π≅ : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ)
        → (e : typ A ≃ typ B)
        → fst e (pt A) ≡ pt B
        → GroupEquiv (πGr n A) (πGr n B)
  ∙≃→π≅ {A = A} {B = B} n e =
    EquivJ (λ A e → (a : A) → fst e a ≡ pt B
                  → GroupEquiv (πGr n (A , a)) (πGr n B))
      (λ b p → J (λ b p → GroupEquiv (πGr n (typ B , b)) (πGr n B))
        idGroupEquiv (sym p))
      e (pt A)

{- π₄(S³) ≅ π₃((S² × S²) ⊔ᴬ S²)
  where A = S² ∨ S² -}
π₄S³≅π₃PushS² :
  GroupIso (πGr 3 (S₊∙ 3))
           (πGr 2 (Pushout⋁↪fold⋁∙ (S₊∙ 2)))
π₄S³≅π₃PushS² =
  compGroupIso
    (GroupEquiv→GroupIso
     (∙≃→π≅ 3 (compEquiv (isoToEquiv (invIso IsoS³S3)) S³≃SuspS²) refl))
    (compGroupIso
     (invGroupIso (GrIso-πΩ-π 2))
     (compGroupIso
       (πTruncGroupIso 2)
       (compGroupIso
         (GroupEquiv→GroupIso
          (∙≃→π≅ {B = _ , ∣ inl (base , base) ∣ₕ}
           2 (isoToEquiv IsoΩ∥SuspS²∥₅∥Pushout⋁↪fold⋁S²∥₅) encode∙))
         (compGroupIso
         (invGroupIso (πTruncGroupIso 2))
          (GroupEquiv→GroupIso (invEq (GroupPath _ _)
           (cong (πGr 2)
            (cong Pushout⋁↪fold⋁∙ (ua∙ S²≃SuspS¹ refl)))))))))
  where
  encode∙ : encode ∣ north ∣ refl ≡ ∣ inl (base , base) ∣
  encode∙ = transportRefl _
