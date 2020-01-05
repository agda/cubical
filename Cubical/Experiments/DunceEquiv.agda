{-

Trying to show that Dunce ≃ DunceCone without using contractibility

-}
{-# OPTIONS --cubical #-}

module Cubical.Experiments.DunceEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.S1 using (S¹; base)
import Cubical.HITs.S1 as S¹

open import Cubical.HITs.MappingCones
open import Cubical.HITs.DunceCap


data Dunce₁ : Type₀ where
  inj₁ : S¹ → Dunce₁
  surf₁ : (λ i → inj₁ (dunceMap (S¹.loop i))) ≡ refl

sides₁ : (i j : I) → I → Partial (~ i ∨ i ∨ ~ j ∨ j) DunceCone
sides₁ i j k (i = i0) = inj (dunceMap (S¹.loop j))
sides₁ i j k (i = i1) = spoke base k
sides₁ i j k (j = i0) = spoke base (~ i ∨ k)
sides₁ i j k (j = i1) = spoke base (~ i ∨ k)

DunceCone-iso-Dunce₁ : Iso DunceCone Dunce₁
Iso.fun DunceCone-iso-Dunce₁ (inj x)               = inj₁ x
Iso.fun DunceCone-iso-Dunce₁ hub                   = inj₁ base
Iso.fun DunceCone-iso-Dunce₁ (spoke base i)        = inj₁ base
Iso.fun DunceCone-iso-Dunce₁ (spoke (S¹.loop j) i) = surf₁ (~ i) j
Iso.inv DunceCone-iso-Dunce₁ (inj₁ x)    = inj x
Iso.inv DunceCone-iso-Dunce₁ (surf₁ i j)
  = hcomp (sides₁ i j) (spoke (S¹.loop j) (~ i))
Iso.leftInv DunceCone-iso-Dunce₁ (inj x) i               = inj x
Iso.leftInv DunceCone-iso-Dunce₁ hub i                   = spoke base (~ i)
Iso.leftInv DunceCone-iso-Dunce₁ (spoke base i) j        = spoke base (i ∨ ~ j)
Iso.leftInv DunceCone-iso-Dunce₁ (spoke (S¹.loop j) i) k
  = hfill (sides₁ (~ i) j) (inS (spoke (S¹.loop j) i)) (~ k)
Iso.rightInv DunceCone-iso-Dunce₁ (inj₁ x) i    = inj₁ x
Iso.rightInv DunceCone-iso-Dunce₁ (surf₁ i j) k
  = hfill (λ k o → Iso.fun DunceCone-iso-Dunce₁ (sides₁ i j k o)) (inS (surf₁ i j)) (~ k)

data Dunce₂ : Type₀ where
  base₂ : Dunce₂
  loop₂ : base₂ ≡ base₂
  surf₂ : (λ i → loop₂ i) ⁻¹ ∙∙ (λ i → loop₂ i) ∙∙ (λ i → loop₂ i) ≡ refl

inj₂ : S¹ → Dunce₂
inj₂ base = base₂
inj₂ (S¹.loop i) = loop₂ i



-- to be moved to another file
module _ {ℓ ℓ'} {A : Type ℓ} {w x y z : A} {B : Type ℓ'} where

  cong-∙ : ∀ (f : A → B) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
  cong-∙ f p q j i = hcomp (λ k → λ { (j = i0) → f (compPath-filler p q k i)
                                    ; (i = i0) → f x
                                    ; (i = i1) → f (q k) })
                           (f (p i))

  cong-∙∙ : ∀ (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
  cong-∙∙ f p q r j i = hcomp (λ k → λ { (j = i0) → f (doubleCompPath-filler p q r i k)
                                       ; (i = i0) → f (p (~ k))
                                       ; (i = i1) → f (r k) })
                              (f (q i))

-- private
--   eq₂ : ∀ {ℓ} {A : Type ℓ} (f : S¹ → A) →
--         ((λ i → f (dunceMap (S¹.loop i))) ≡ refl) ≡
--         ((λ i → f (S¹.loop i)) ⁻¹ ∙∙ (λ i → f (S¹.loop i)) ∙∙ (λ i → f (S¹.loop i)) ≡ refl)
--   eq₂ f = cong (_≡ refl) (cong-∙∙ f (sym (S¹.loop)) S¹.loop S¹.loop)

sides₂ : ∀ {ℓ} {A : Type ℓ} (f : S¹ → A) (i j : I) → I → Partial (~ i ∨ i ∨ ~ j ∨ j) A
sides₂ f i j k (i = i0) = cong-∙∙ f (sym S¹.loop) S¹.loop S¹.loop k j
sides₂ f i j k (i = i1) = f base
sides₂ f i j k (j = i0) = f base
sides₂ f i j k (j = i1) = f base

Dunce₁-iso-Dunce₂ : Iso Dunce₁ Dunce₂
Iso.fun Dunce₁-iso-Dunce₂ (inj₁ x) = inj₂ x
Iso.fun Dunce₁-iso-Dunce₂ (surf₁ i j)
  = hcomp (λ k → sides₂ inj₂ i j (~ k)) (surf₂ i j)
  -- = transport⁻ (eq₂ inj₂) surf₂ i j
Iso.inv Dunce₁-iso-Dunce₂ base₂ = inj₁ base
Iso.inv Dunce₁-iso-Dunce₂ (loop₂ i) = inj₁ (S¹.loop i)
Iso.inv Dunce₁-iso-Dunce₂ (surf₂ i j)
  = hcomp (λ k → sides₂ inj₁ i j    k ) (surf₁ i j)
  -- = transport  (eq₂ inj₁) surf₁ i j
Iso.rightInv Dunce₁-iso-Dunce₂ base₂ i = base₂
Iso.rightInv Dunce₁-iso-Dunce₂ (loop₂ i) j = loop₂ i
Iso.rightInv Dunce₁-iso-Dunce₂ (surf₂ i j) k
  = {!!}
  -- = hfill {φ = ~ i ∨ i ∨ ~ j ∨ j} (λ k o → Iso.fun Dunce₁-iso-Dunce₂ (sides₂ inj₁ i j k o)) -- ? (~ k)
  --         ? (~ k) -- (inS (hfill (λ k → sides₂ inj₂ i j (~ k)) (inS (surf₂ i j)) (~ k))) (~ k)
Iso.leftInv Dunce₁-iso-Dunce₂ (inj₁ base) i = inj₁ base
Iso.leftInv Dunce₁-iso-Dunce₂ (inj₁ (S¹.loop i)) j = inj₁ (S¹.loop i)
Iso.leftInv Dunce₁-iso-Dunce₂ (surf₁ i j) k
  = {!!}
  -- = hfill (λ k o → transp (λ _ → Dunce₁) k (Iso.inv Dunce₁-iso-Dunce₂ (sides₂ inj₂ i j (~ k) o)))
  --         (?) (~ k) -- transp (λ _ → Dunce₁) i0 ?) (~ k)

-- transp (λ l → eq inj₂ (~ l ∧ ~ k)) k (transp (λ l → eq inj₁ (l ∧ ~ k)) k surf₁ i j) i j

-- to be moved to another file
module _ {ℓ} {A : Type ℓ} {w x y z : A}  where

  PathP≡compPath : ∀ (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                   → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
  PathP≡compPath p q r k = PathP (λ i → x ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

  PathP≡doubleCompPath : ∀ (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                         → (PathP (λ i → p i ≡ s i) q r) ≡ (p ⁻¹ ∙∙ q ∙∙ s ≡ r)
  PathP≡doubleCompPath p q r s k = PathP (λ i → p (i ∨ k) ≡ s (i ∨ k)) (λ j → doubleCompPath-filler (p ⁻¹) q s j k) r

private
  eq₃ : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → (PathP (λ i → p i ≡ p i) p refl) ≡ (p ⁻¹ ∙∙ p ∙∙ p ≡ refl)
  eq₃ p = PathP≡doubleCompPath p p refl p

Dunce₂-iso-Dunce : Iso Dunce₂ Dunce
Iso.fun Dunce₂-iso-Dunce base₂ = base
Iso.fun Dunce₂-iso-Dunce (loop₂ i) = loop i
Iso.fun Dunce₂-iso-Dunce (surf₂ i j) = transport (eq₃ loop ) surf  i j
Iso.inv Dunce₂-iso-Dunce base = base₂
Iso.inv Dunce₂-iso-Dunce (loop i) = loop₂ i
Iso.inv Dunce₂-iso-Dunce (surf i j) = transport⁻ (eq₃ loop₂) surf₂ i j
Iso.leftInv Dunce₂-iso-Dunce base₂ = refl
Iso.leftInv Dunce₂-iso-Dunce (loop₂ i) = refl
Iso.leftInv Dunce₂-iso-Dunce (surf₂ i j) = {!!}
Iso.rightInv Dunce₂-iso-Dunce base = refl
Iso.rightInv Dunce₂-iso-Dunce (loop i) = refl
Iso.rightInv Dunce₂-iso-Dunce (surf i j) = {!!}

DunceCone-iso-Dunce : Iso DunceCone Dunce
DunceCone-iso-Dunce = compIso DunceCone-iso-Dunce₁ (compIso Dunce₁-iso-Dunce₂ Dunce₂-iso-Dunce)

DunceCone≡Dunce : DunceCone ≡ Dunce
DunceCone≡Dunce = isoToPath DunceCone-iso-Dunce
