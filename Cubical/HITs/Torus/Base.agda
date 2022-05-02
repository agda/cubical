{-

Definition of the torus as a HIT together with a proof that it is
equivalent to two circles

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.Torus.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Sigma

open import Cubical.HITs.S1

data Torus : Type₀ where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

t2c : Torus → S¹ × S¹
t2c point        = ( base , base )
t2c (line1 i)    = ( loop i , base )
t2c (line2 j)    = ( base , loop j )
t2c (square i j) = ( loop i , loop j )

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : ∀ (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl

Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

point-path : PathP (λ i → Torus≡S¹×S¹ i) point (base , base)
point-path i =
  (glue (λ {
   (i = i0) → point;
   (i = i1) → (base , base) }) (base , base))

Loop : {A : Type₀} (p : A) → Type₀
Loop p = p ≡ p

ΩTorus : Type₀
ΩTorus = Loop point

-- TODO: upstream
lemPathAnd : ∀ {ℓ} {A B : Type ℓ} (t u : A × B) →
  Path _ (t ≡ u) ((t .fst ≡ u .fst) × ((t .snd) ≡ (u .snd)))
lemPathAnd t u = isoToPath (iso (λ tu → (λ i → tu i .fst) , λ i → tu i .snd)
                                 (λ tu i → tu .fst i , tu .snd i)
                                 (λ y → refl)
                                 (λ x → refl))

ΩTorus≡ℤ×ℤ : ΩTorus ≡ ℤ × ℤ
ΩTorus≡ℤ×ℤ =
  ΩTorus
    ≡⟨ (λ i → Loop (point-path i)) ⟩
  Loop (base , base)
    ≡⟨ lemPathAnd (base , base) (base , base) ⟩
  ΩS¹ × ΩS¹
    ≡⟨ (λ i → ΩS¹≡ℤ i × ΩS¹≡ℤ i) ⟩
  ℤ × ℤ ∎

-- Computing the winding numbers on the torus
windingTorus : ΩTorus → ℤ × ℤ
windingTorus l = ( winding (λ i → t2c (l i) .fst)
                 , winding (λ i → t2c (l i) .snd))

module _ where
 private
  test1 : windingTorus (line1 ∙ line2) ≡ (pos 1 , pos 1)
  test1 = refl

  test2 : windingTorus (line1 ∙ line2 ∙ sym line1 ∙ sym line1) ≡ (negsuc 0 , pos 1)
  test2 = refl
