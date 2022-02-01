{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (_∈_)

open import Cubical.HITs.SetQuotients hiding (_/_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.QuotientRing renaming (_/_ to _/Ring_) hiding ([_]/)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal using (isIdeal)

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommRingStr {{...}} hiding (_-_; -_; dist; ·Lid; ·Rdist+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (CommAlgebra→CommRing A)) using (-DistR·)
  instance
    _ : CommRingStr _
    _ = snd R
    _ : CommAlgebraStr _ _
    _ = snd A

  _/_ : (I : IdealsIn A) → CommAlgebra R ℓ
  _/_ I = commAlgebraFromCommRing
           ((CommAlgebra→CommRing A) /Ring I)
           (λ r → elim (λ _ → squash/) (λ x → [ r ⋆ x ]) (eq r))
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r ·R s) ⋆ x ≡⟨ ⋆-assoc r s x ⟩
                                         r ⋆ (s ⋆ x) ∎) i ])
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r +R s) ⋆ x ≡⟨ ⋆-ldist r s x ⟩
                                       r ⋆ x + s ⋆ x ∎) i ])
           (λ r → elimProp2 (λ _ _ → squash/ _ _)
                            λ x y i → [ (r ⋆ (x + y)  ≡⟨ ⋆-rdist r x y ⟩
                                        r ⋆ x + r ⋆ y ∎) i ])
           (elimProp (λ _ → squash/ _ _)
                     (λ x i →  [ (1r ⋆ x ≡⟨ ⋆-lid x ⟩ x ∎) i ]))
           λ r → elimProp2 (λ _ _ → squash/ _ _)
                           λ x y i → [ ((r ⋆ x) · y ≡⟨ ⋆-lassoc r x y ⟩
                                       r ⋆ (x · y) ∎) i ]

          where
                eq : (r : fst R) (x y : fst A) → x - y ∈ (fst I) →  [ r ⋆ x ] ≡ [ r ⋆ y ]
                eq r x y x-y∈I = eq/ _ _
                  (subst (λ u → u ∈ fst I)
                  ((r ⋆ 1a) · (x - y)               ≡⟨ ·Rdist+ (r ⋆ 1a) x (- y)  ⟩
                    (r ⋆ 1a) · x + (r ⋆ 1a) · (- y) ≡[ i ]⟨ (r ⋆ 1a) · x + -DistR· (r ⋆ 1a) y i ⟩
                    (r ⋆ 1a) · x - (r ⋆ 1a) · y     ≡[ i ]⟨ ⋆-lassoc r 1a x i
                                                            - ⋆-lassoc r 1a y i ⟩
                    r ⋆ (1a · x) - r ⋆ (1a · y)     ≡[ i ]⟨ r ⋆ (·Lid x i) - r ⋆ (·Lid y i) ⟩
                    r ⋆ x - r ⋆ y ∎ )
                  (isIdeal.·-closedLeft (snd I) _ x-y∈I))


[_]/ : {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
       → (a : fst A) → fst (A / I)
[ a ]/ = [ a ]
