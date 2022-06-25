{-# OPTIONS --safe #-}
module Cubical.Homotopy.HSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1
open import Cubical.HITs.Sn

record HSpace {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  constructor HSp
  field
    μ : typ A → typ A → typ A
    μₗ : (x : typ A) → μ (pt A) x ≡ x
    μᵣ : (x : typ A) → μ x (pt A) ≡ x
    μₗᵣ : μₗ (pt A) ≡ μᵣ (pt A)

record AssocHSpace {ℓ : Level} {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor AssocHSp
  field
    μ-assoc : (x y z : _)
      → HSpace.μ e (HSpace.μ e x y) z ≡ HSpace.μ e x (HSpace.μ e y z)

    μ-assoc-filler : (y z : typ A)
      → PathP (λ i → HSpace.μ e (HSpace.μₗ e y i) z
                    ≡ HSpace.μₗ e (HSpace.μ e y z) i)
               (μ-assoc (pt A) y z)
               refl

record LeftInvHSpace {ℓ : Level} {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor LeftInvHSp
  field
    μ-equiv : (x : typ A) → isEquiv (HSpace.μ e x)

  -- every left-invertible H-space is strongly homogeneous
  isHomogeneousHSp : isHomogeneous A
  isHomogeneousHSp x = pointed-sip A (fst A , x)
                       ((HSpace.μ e x , μ-equiv x) , HSpace.μᵣ e x)

{- H-space structures on A are exactly pointed sections of the evaluation map,
   expressed here with a pointed Π-type -}
HSpace-Π∙-Iso : {ℓ : Level} (A : Pointed ℓ) → Iso (HSpace A)
                (Π∙ A (λ x → A →∙ (typ A , x)) (idfun∙ A))
fst (fst (Iso.fun (HSpace-Π∙-Iso A) e) x) = HSpace.μ e x
snd (fst (Iso.fun (HSpace-Π∙-Iso A) e) x) = HSpace.μᵣ e x
fst (snd (Iso.fun (HSpace-Π∙-Iso A) e) i) x = HSpace.μₗ e x i
snd (snd (Iso.fun (HSpace-Π∙-Iso A) e) i) j = invEq slideSquareEquiv
  (flipSquare (HSpace.μₗᵣ e)) i j
HSpace.μ (Iso.inv (HSpace-Π∙-Iso A) s) x = fst (fst s x)
HSpace.μₗ (Iso.inv (HSpace-Π∙-Iso A) s) x i = fst (snd s i) x
HSpace.μᵣ (Iso.inv (HSpace-Π∙-Iso A) s) x = snd (fst s x)
HSpace.μₗᵣ (Iso.inv (HSpace-Π∙-Iso A) s) = flipSquare
  (equivFun slideSquareEquiv (λ i j → snd (snd s i) j))
fst (fst (Iso.rightInv (HSpace-Π∙-Iso A) s k) x) = fst (fst s x)
snd (fst (Iso.rightInv (HSpace-Π∙-Iso A) s k) x) = snd (fst s x)
fst (snd (Iso.rightInv (HSpace-Π∙-Iso A) s k) i) x = fst (snd s i) x
snd (snd (Iso.rightInv (HSpace-Π∙-Iso A) s k) i) j = retEq slideSquareEquiv
  (λ i' j' → snd (snd s i') j') k i j
HSpace.μ (Iso.leftInv (HSpace-Π∙-Iso A) e k) x = HSpace.μ e x
HSpace.μₗ (Iso.leftInv (HSpace-Π∙-Iso A) e k) x = HSpace.μₗ e x
HSpace.μᵣ (Iso.leftInv (HSpace-Π∙-Iso A) e k) x = HSpace.μᵣ e x
HSpace.μₗᵣ (Iso.leftInv (HSpace-Π∙-Iso A) e k) = flipSquare
  (secEq slideSquareEquiv (flipSquare (HSpace.μₗᵣ e)) k)

HSpace-Π∙-Equiv : {ℓ : Level} (A : Pointed ℓ) → HSpace A ≃
                  Π∙ A (λ x → A →∙ (typ A , x)) (idfun∙ A)
HSpace-Π∙-Equiv A = isoToEquiv (HSpace-Π∙-Iso A)

-- Instances
open HSpace
open AssocHSpace

-- S¹
S1-HSpace : HSpace (S₊∙ 1)
μ S1-HSpace = _·_
μₗ S1-HSpace x = refl
μᵣ S1-HSpace base = refl
μᵣ S1-HSpace (loop i) = refl
μₗᵣ S1-HSpace x = refl

S1-AssocHSpace : AssocHSpace S1-HSpace
μ-assoc S1-AssocHSpace base _ _ = refl
μ-assoc S1-AssocHSpace (loop i) x y j = h x y j i
  where
  h : (x y : S₊ 1) → cong (_· y) (rotLoop x) ≡ rotLoop (x · y)
  h = wedgeconFun _ _ (λ _ _ → isOfHLevelPath 2 (isGroupoidS¹ _ _) _ _)
        (λ x → refl)
        (λ { base → refl ; (loop i) → refl})
        refl
μ-assoc-filler S1-AssocHSpace _ _ = refl
