{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Cylinder.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Everything

open import Cubical.HITs.PropositionalTruncation

import Cubical.Data.Everything as Data
open Data hiding (inl; inr)

open import Cubical.HITs.Interval

-- Cylinder A is a cylinder object in the category of cubical types.
--
--   https://ncatlab.org/nlab/show/cylinder+object
data Cylinder {ℓ} (A : Type ℓ) : Type ℓ where
  inl : A → Cylinder A
  inr : A → Cylinder A
  cross : ∀ x → inl x ≡ inr x

-- Dual to this is the cocylinder or path space object.
--
--   https://ncatlab.org/nlab/show/path+space+object
Cocylinder : ∀ {ℓ} → Type ℓ → Type ℓ
Cocylinder A = Interval → A

module _ {ℓ} {A : Type ℓ} where
  -- The cylinder is part of a factorization of the obvious mapping
  -- of type A ⊎ A → A into a pair of mappings:
  --
  --   A ⊎ A → Cylinder A ≃ A
  --
  -- include is the first part of the factorization.
  include : A ⊎ A → Cylinder A
  include (Data.inl x) = inl x
  include (Data.inr x) = inr x

  -- The above inclusion is surjective
  includeSurjective : ∀ c → ∥ Σ[ s ∈ A ⊎ A ] include s ≡ c ∥
  includeSurjective (inl x) = ∣ Data.inl x , refl ∣
  includeSurjective (inr x) = ∣ Data.inr x , refl ∣
  includeSurjective (cross x i) =
    squash
      ∣ Data.inl x , (λ j → cross x (i ∧ j)) ∣
      ∣ Data.inr x , (λ j → cross x (i ∨ ~ j)) ∣
      i

  elimCyl
    : ∀{ℓ'} {B : Cylinder A → Type ℓ'}
    → (f : (x : A) → B (inl x))
    → (g : (x : A) → B (inr x))
    → (p : ∀ x → PathP (λ i → B (cross x i)) (f x) (g x))
    → (c : Cylinder A) → B c
  elimCyl f _ _ (inl x) = f x
  elimCyl _ g _ (inr x) = g x
  elimCyl _ _ p (cross x i) = p x i

  private
    out : Cylinder A → A
    out (inl x) = x
    out (inr x) = x
    out (cross x i) = x

    inl-out : (c : Cylinder A) → inl (out c) ≡ c
    inl-out (inl x) = refl
    inl-out (inr x) = cross x
    inl-out (cross x i) = λ j → cross x (i ∧ j)

    out-inl : ∀(x : A) → out (inl x) ≡ x
    out-inl x = refl

  -- The second part of the factorization above.
  CylinderA≃A : Cylinder A ≃ A
  CylinderA≃A = isoToEquiv (iso out inl out-inl inl-out)

  -- The cocylinder has a similar equivalence that is part
  -- of factorizing the diagonal mapping.
  private
    inco : A → Cocylinder A
    inco x _ = x

    outco : Cocylinder A → A
    outco f = f zero

    A→CocylinderA→A : (x : A) → outco (inco x) ≡ x
    A→CocylinderA→A x = refl

    CocylinderA→A→CocylinderA : (c : Cocylinder A) → inco (outco c) ≡ c
    CocylinderA→A→CocylinderA c j zero = c zero
    CocylinderA→A→CocylinderA c j one = c (seg j)
    CocylinderA→A→CocylinderA c j (seg i) = c (seg (j ∧ i))

  A≃CocylinderA : A ≃ Cocylinder A
  A≃CocylinderA =
    isoToEquiv (iso inco outco CocylinderA→A→CocylinderA A→CocylinderA→A)

  project : Cocylinder A → A × A
  project c = c zero , c one


-- Since we can construct cylinders for every type, Cylinder actually
-- constitutes a cylinder functor:
--
--   https://ncatlab.org/nlab/show/cylinder+functor
--
-- e₀ = inl
-- e₁ = inr
-- σ = out
module Functorial where
  private
    variable
      ℓa ℓb ℓc : Level
      A : Type ℓa
      B : Type ℓb
      C : Type ℓc

  mapCylinder : (A → B) → Cylinder A → Cylinder B
  mapCylinder f (inl x) = inl (f x)
  mapCylinder f (inr x) = inr (f x)
  mapCylinder f (cross x i) = cross (f x) i

  mapCylinderId : mapCylinder (λ(x : A) → x) ≡ (λ x → x)
  mapCylinderId i (inl x) = inl x
  mapCylinderId i (inr x) = inr x
  mapCylinderId i (cross x j) = cross x j

  mapCylinder∘
    : (f : A → B) → (g : B → C)
    → mapCylinder (λ x → g (f x)) ≡ (λ x → mapCylinder g (mapCylinder f x))
  mapCylinder∘ f g i (inl x) = inl (g (f x))
  mapCylinder∘ f g i (inr x) = inr (g (f x))
  mapCylinder∘ f g i (cross x j) = cross (g (f x)) j

  -- There is an adjunction between the cylinder and coyclinder
  -- functors.
  --
  --   Cylinder ⊣ Cocylinder
  adj₁ : (Cylinder A → B) → A → Cocylinder B
  adj₁ f x zero = f (inl x)
  adj₁ f x one = f (inr x)
  adj₁ f x (seg i) = f (cross x i)

  adj₂ : (A → Cocylinder B) → Cylinder A → B
  adj₂ g (inl x) = g x zero
  adj₂ g (inr x) = g x one
  adj₂ g (cross x i) = g x (seg i)

  adj₁₂ : (g : A → Cocylinder B) → adj₁ (adj₂ g) ≡ g
  adj₁₂ g _ x zero = g x zero
  adj₁₂ g _ x one = g x one
  adj₁₂ g _ x (seg i) = g x (seg i)

  adj₂₁ : (f : Cylinder A → B) → adj₂ (adj₁ f) ≡ f
  adj₂₁ f j (inl x) = f (inl x)
  adj₂₁ f j (inr x) = f (inr x)
  adj₂₁ f j (cross x i) = f (cross x i)

module IntervalEquiv where
  -- There is an equivalence between the interval and the
  -- cylinder over the unit type.
  Interval→CylinderUnit : Interval → Cylinder Unit
  Interval→CylinderUnit zero = inl _
  Interval→CylinderUnit one = inr _
  Interval→CylinderUnit (seg i) = cross _ i

  CylinderUnit→Interval : Cylinder Unit → Interval
  CylinderUnit→Interval (inl _) = zero
  CylinderUnit→Interval (inr _) = one
  CylinderUnit→Interval (cross _ i) = seg i

  Interval→CylinderUnit→Interval
    : ∀ i → CylinderUnit→Interval (Interval→CylinderUnit i) ≡ i
  Interval→CylinderUnit→Interval zero = refl
  Interval→CylinderUnit→Interval one = refl
  Interval→CylinderUnit→Interval (seg i) = refl

  CylinderUnit→Interval→CylinderUnit
    : ∀ c → Interval→CylinderUnit (CylinderUnit→Interval c) ≡ c
  CylinderUnit→Interval→CylinderUnit (inl _) = refl
  CylinderUnit→Interval→CylinderUnit (inr _) = refl
  CylinderUnit→Interval→CylinderUnit (cross _ i) = refl

  CylinderUnit≃Interval : Cylinder Unit ≃ Interval
  CylinderUnit≃Interval =
    isoToEquiv (iso CylinderUnit→Interval Interval→CylinderUnit Interval→CylinderUnit→Interval CylinderUnit→Interval→CylinderUnit)


  -- More generally, there is an equivalence between the cylinder
  -- over any type A and the product of A and the interval.
  module _ {ℓ} {A : Type ℓ} where
    private
      Cyl : Type ℓ
      Cyl = A × Interval

    CylinderA→A×Interval : Cylinder A → Cyl
    CylinderA→A×Interval (inl x) = x , zero
    CylinderA→A×Interval (inr x) = x , one
    CylinderA→A×Interval (cross x i) = x , seg i

    A×Interval→CylinderA : Cyl → Cylinder A
    A×Interval→CylinderA (x , zero) = inl x
    A×Interval→CylinderA (x , one) = inr x
    A×Interval→CylinderA (x , seg i) = cross x i

    A×Interval→CylinderA→A×Interval
      : ∀ c → CylinderA→A×Interval (A×Interval→CylinderA c) ≡ c
    A×Interval→CylinderA→A×Interval (x , zero) = refl
    A×Interval→CylinderA→A×Interval (x , one) = refl
    A×Interval→CylinderA→A×Interval (x , seg i) = refl

    CylinderA→A×Interval→CylinderA
      : ∀ c → A×Interval→CylinderA (CylinderA→A×Interval c) ≡ c
    CylinderA→A×Interval→CylinderA (inl x) = refl
    CylinderA→A×Interval→CylinderA (inr x) = refl
    CylinderA→A×Interval→CylinderA (cross x i) = refl

    CylinderA≃A×Interval : Cylinder A ≃ Cyl
    CylinderA≃A×Interval =
      isoToEquiv
        (iso CylinderA→A×Interval
             A×Interval→CylinderA
             A×Interval→CylinderA→A×Interval
             CylinderA→A×Interval→CylinderA)

-- The cylinder is also the pushout of the identity on A with itself.
module Push {ℓ} {A : Type ℓ} where
  open import Cubical.HITs.Pushout

  private
    Push : Type ℓ
    Push = Pushout (λ(x : A) → x) (λ x → x)

    Cyl : Type ℓ
    Cyl = Cylinder A

  Cylinder→Pushout : Cyl → Push
  Cylinder→Pushout (inl x) = inl x
  Cylinder→Pushout (inr x) = inr x
  Cylinder→Pushout (cross x i) = push x i

  Pushout→Cylinder : Push → Cyl
  Pushout→Cylinder (inl x) = inl x
  Pushout→Cylinder (inr x) = inr x
  Pushout→Cylinder (push x i) = cross x i

  Pushout→Cylinder→Pushout : ∀ p → Cylinder→Pushout (Pushout→Cylinder p) ≡ p
  Pushout→Cylinder→Pushout (inl x) = refl
  Pushout→Cylinder→Pushout (inr x) = refl
  Pushout→Cylinder→Pushout (push x i) = refl

  Cylinder→Pushout→Cylinder : ∀ c → Pushout→Cylinder (Cylinder→Pushout c) ≡ c
  Cylinder→Pushout→Cylinder (inl x) = refl
  Cylinder→Pushout→Cylinder (inr x) = refl
  Cylinder→Pushout→Cylinder (cross x i) = refl

  Pushout≃Cylinder : Push ≃ Cyl
  Pushout≃Cylinder =
    isoToEquiv
      (iso Pushout→Cylinder
           Cylinder→Pushout
           Cylinder→Pushout→Cylinder
           Pushout→Cylinder→Pushout)

