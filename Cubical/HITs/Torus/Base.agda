{-

Definition of the torus as a HIT together with a proof that it is
equivalent to two circles

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Torus.Base where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int
open import Cubical.Data.Prod hiding (_×_) renaming (_×Σ_ to _×_)

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

ΩTorus : Type₀
ΩTorus = point ≡ point

-- TODO: upstream
lemPathAnd : ∀ {ℓ} {A B : Type ℓ} (t u : A × B) →
  Path _ (t ≡ u) ((t .fst ≡ u .fst) × ((t .snd) ≡ (u .snd)))
lemPathAnd t u = isoToPath (iso (λ tu → (λ i → tu i .fst) , λ i → tu i .snd)
                                 (λ tu i → tu .fst i , tu .snd i)
                                 (λ y → refl)
                                 (λ x → refl))

funDep : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (u0 : A) (u1 : B) →
  (Path A u0 (transport (λ i → p (~ i)) u1)) ≡ (Path B (transport p u0) u1)
funDep p u0 u1 i = Path (p i) (transp (λ j → p (i ∧ j)) (~ i) u0) (transp (λ j → p (i ∨ ~ j)) i u1)

-- Can this proof be simplified?
ΩTorus≡Int×Int : ΩTorus ≡ Int × Int
ΩTorus≡Int×Int =
  ΩTorus
    ≡⟨ (λ i → Path Torus point (transp (\ j → Torus≡S¹×S¹ (~ j ∧ i)) (~ i)
                                       (glue (λ { (i = i0) → point
                                                ; (i = i1) → (base , base) }) (base , base)))) ⟩
  Path Torus point (transp (\ i → Torus≡S¹×S¹ (~ i)) i0 (base , base))
    ≡⟨ funDep (λ i → Torus≡S¹×S¹ i) point (base , base) ⟩
  Path (S¹ × S¹) (transp (\ i → Torus≡S¹×S¹ i) i0 point) (base , base)
    ≡⟨ (λ i → Path _ (transp (λ j → Torus≡S¹×S¹ (j ∨ i))  i
                             (glue (λ { (i = i0) → point
                                      ; (i = i1) → (base , base) }) (base , base))) (base , base)) ⟩
  Path (S¹ × S¹) (base , base) (base , base)
    ≡⟨ lemPathAnd (base , base) (base , base) ⟩
  ΩS¹ × ΩS¹
    ≡⟨ (λ i → ΩS¹≡Int i × ΩS¹≡Int i) ⟩
  Int × Int ∎
