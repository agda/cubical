module Cubical.Homotopy.HSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1
open import Cubical.HITs.Sn

private
  variable
    ℓ ℓ' : Level

record HSpace (A : Pointed ℓ) : Type ℓ where
  constructor HSp
  field
    μ : typ A → typ A → typ A
    μₗ : (x : typ A) → μ (pt A) x ≡ x
    μᵣ : (x : typ A) → μ x (pt A) ≡ x
    μₗᵣ : μₗ (pt A) ≡ μᵣ (pt A)

record AssocHSpace {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor AssocHSp
  open HSpace e
  field
    μ-assoc : (x y z : _)
      → μ (μ x y) z ≡ μ x (μ y z)

    μ-assoc-filler : (y z : typ A)
      → PathP (λ i → μ (μₗ y i) z
                    ≡ μₗ (μ y z) i)
               (μ-assoc (pt A) y z)
               refl

record LeftInvHSpace {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor LeftInvHSp
  open HSpace e
  field
    μ-equiv : (x : typ A) → isEquiv (μ x)

  μ≃ : typ A → typ A ≃ typ A
  μ≃ x = (μ x , μ-equiv x)

  μ⁻¹ : typ A → typ A → typ A
  μ⁻¹ x = invIsEq (μ-equiv x)

  μ⁻¹ₗ : (x : typ A) → μ⁻¹ (pt A) x ≡ x
  μ⁻¹ₗ x = sym (invEq (equivAdjointEquiv (μ≃ (pt A))) (μₗ x))

  μ⁻¹ᵣ : (x : typ A) → μ⁻¹ x x ≡ (pt A)
  μ⁻¹ᵣ x = sym (invEq (equivAdjointEquiv (μ≃ x)) (μᵣ x))

  -- every left-invertible H-space is (strongly) homogeneous
  isHomogeneousHSp : isHomogeneous A
  isHomogeneousHSp x = pointed-sip A (fst A , x)
                       ((μ x , μ-equiv x) , μᵣ x)

module _ {A : Pointed ℓ} {B : Pointed ℓ'} (hb : HSpace B)
         (hi : LeftInvHSpace hb) where

  open HSpace hb
  open LeftInvHSpace hi

  -- this could be given a direct proof
  →∙HSpace≡ : {f g : A →∙ B} → f .fst ≡ g .fst → f ≡ g
  →∙HSpace≡ {f} {g} p = →∙Homogeneous≡ isHomogeneousHSp p

{- H-space structures on A are exactly pointed sections of the evaluation map,
   expressed here with a pointed Π-type -}
HSpace-Π∙-Iso : (A : Pointed ℓ) → Iso (HSpace A)
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

HSpace-Π∙-Equiv : (A : Pointed ℓ) → HSpace A ≃
                  Π∙ A (λ x → A →∙ (typ A , x)) (idfun∙ A)
HSpace-Π∙-Equiv A = isoToEquiv (HSpace-Π∙-Iso A)

{- every (strongly) homogeneous structure on A gives rise
   to a left-invertible H-space structure, by a slight modification -}
HSpace-homogeneous : (A : Pointed ℓ) → isHomogeneous A → HSpace A
HSpace-homogeneous A h = Iso.inv (HSpace-Π∙-Iso A) s
  where
    k : (x : typ A) → A ≃∙ (typ A , x)
    k x = pointed-sip⁻ A (typ A , x) (sym (h (pt A)) ∙ h x)

    k₀ : k (pt A) ≡ idEquiv∙ A
    k₀ = congS (pointed-sip⁻ A A) (lCancel (h (pt A))) ∙ pointed-sip⁻-refl A

    s : Π∙ A (λ x → A →∙ (typ A , x)) (idfun∙ A)
    fst s x = ≃∙map (k x)
    snd s = congS ≃∙map k₀

LeftInvHSpace-homogeneous : (A : Pointed ℓ) → (h : isHomogeneous A)
                            → LeftInvHSpace (HSpace-homogeneous A h)
LeftInvHSpace.μ-equiv (LeftInvHSpace-homogeneous A h) x =
  equivIsEquiv (fst (pointed-sip⁻ A (typ A , x) (sym (h (pt A)) ∙ h x)))

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

-- →∙
module _ (A : Pointed ℓ) (X : Pointed ℓ') (hX : HSpace X) where

  open HSpace hX renaming (μ to μX ; μₗ to μXₗ ; μᵣ to μXᵣ ; μₗᵣ to μXₗᵣ)

  →∙-HSpace : HSpace (A →∙ X ∙)
  fst (μ →∙-HSpace f g) a = μX (f .fst a) (g .fst a)
  snd (μ →∙-HSpace f g) =
    (λ i → μX (f .snd i) (g .fst (pt A))) ∙∙ μXₗ (g .fst (pt A)) ∙∙ g .snd
  fst (μₗ →∙-HSpace g i) a = μXₗ (g .fst a) i
  snd (μₗ →∙-HSpace g i) j = hcomp
    (λ k → λ { (i = i0) → doubleCompPath-filler refl (μXₗ (g .fst (pt A))) (g .snd) k j
             ; (i = i1) → g .snd (j ∧ k)
             ; (j = i0) → μXₗ (g .fst (pt A)) i
             ; (j = i1) → g .snd k})
    (μXₗ (g .fst (pt A)) (i ∨ j))
  fst (μᵣ →∙-HSpace f i) a = μXᵣ (f .fst a) i
  snd (μᵣ →∙-HSpace f i) j = hcomp
    (λ k → λ { (i = i0) → doubleCompPath-filler (λ i' → μX (f .snd i') (pt X)) (μXₗ (pt X)) refl k j
             ; (i = i1) → f .snd (j ∨ (~ k))
             ; (j = i0) → μXᵣ (f .snd (~ k)) i
             ; (j = i1) → pt X }) (hcomp
       (λ k → λ { (i = i0) → μXₗ (pt X) j
                ; (i = i1) → pt X
                ; (j = i0) → μXₗᵣ k i
                ; (j = i1) → pt X }) (μXₗ (pt X) (i ∨ j)))
  fst (μₗᵣ →∙-HSpace k i) a = μXₗᵣ k i
  snd (μₗᵣ →∙-HSpace k i) j = hcomp
    (λ h → λ { (i = i0) → doubleCompPath-filler refl (μXₗ (pt X)) refl h j
             ; (i = i1) → pt X
             ; (j = i0) → μXₗᵣ k i
             ; (j = i1) → pt X
             ; (k = i0) → k0filler i j h
             ; (k = i1) → k1filler i j h } )
    (cntfiller i j k)
      where
        cntfiller : I → I → I → typ X
        cntfiller i j = hfill
          (λ h → λ { (i = i0) → μXₗ (pt X) j
                   ; (i = i1) → pt X
                   ; (j = i0) → μXₗᵣ h i
                   ; (j = i1) → pt X })
          (inS (μXₗ (pt X) (i ∨ j)))

        k0filler : I → I → I → typ X
        k0filler i j = hfill
          (λ h → λ { (i = i0) → doubleCompPath-filler refl (μXₗ (pt X)) refl h j
                   ; (i = i1) → pt X
                   ; (j = i0) → μXₗ (pt X) i
                   ; (j = i1) → pt X})
          (inS (μXₗ (pt X) (i ∨ j)))

        k1filler : I → I → I → typ X
        k1filler i j = hfill
          (λ h → λ { (i = i0) → doubleCompPath-filler refl (μXₗ (pt X)) refl h j
                   ; (i = i1) → pt X
                   ; (j = i0) → μXᵣ (pt X) i
                   ; (j = i1) → pt X })
          (inS (cntfiller i j i1))
