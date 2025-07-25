module Cubical.Algebra.CommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Base

open import Cubical.Reflection.RecordEquiv


private
  variable
    ℓ ℓ' : Level

open Iso

𝒮ᴰ-CommRing : DUARel (𝒮-Univ ℓ) CommRingStr ℓ
𝒮ᴰ-CommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isCommRing ∣ (λ _ _ → isPropIsCommRing _ _ _ _ _) ])
 where
  open CommRingStr
  open IsCommRingHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

CommRingPath : (R S : CommRing ℓ) → CommRingEquiv R S ≃ (R ≡ S)
CommRingPath = ∫ 𝒮ᴰ-CommRing .UARel.ua

uaCommRing : {A B : CommRing ℓ} → CommRingEquiv A B → A ≡ B
uaCommRing {A = A} {B = B} = equivFun (CommRingPath A B)

CommRingIso : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingIso R S = Σ[ e ∈ Iso (R .fst) (S .fst) ]
                     IsCommRingHom (R .snd) (e .fun) (S .snd)

CommRingEquivIsoCommRingIso : (R : CommRing ℓ) (S : CommRing ℓ') → Iso (CommRingEquiv R S) (CommRingIso R S)
fst (fun (CommRingEquivIsoCommRingIso R S) e) = equivToIso (e .fst)
snd (fun (CommRingEquivIsoCommRingIso R S) e) = e .snd
fst (inv (CommRingEquivIsoCommRingIso R S) e) = isoToEquiv (e .fst)
snd (inv (CommRingEquivIsoCommRingIso R S) e) = e .snd
rightInv (CommRingEquivIsoCommRingIso R S) (e , he) =
  Σ≡Prop (λ e → isPropIsCommRingHom (snd R) (e .fun) (snd S))
         rem
  where
  rem : equivToIso (isoToEquiv e) ≡ e
  fun (rem i) x = fun e x
  inv (rem i) x = inv e x
  rightInv (rem i) b j = CommRingStr.is-set (snd S) (fun e (inv e b)) b (rightInv e b) (rightInv e b) i j
  leftInv (rem i) a j = CommRingStr.is-set (snd R) (inv e (fun e a)) a (retEq (isoToEquiv e) a) (leftInv e a) i j
leftInv (CommRingEquivIsoCommRingIso R S) e =
  Σ≡Prop (λ e → isPropIsCommRingHom (snd R) (e .fst) (snd S))
         (equivEq refl)

isGroupoidCommRing : isGroupoid (CommRing ℓ)
isGroupoidCommRing _ _ = isOfHLevelRespectEquiv 2 (CommRingPath _ _) (isSetCommRingEquiv _ _)


open CommRingStr
open IsCommRingHom
-- TODO: Induced structure results are temporarily inconvenient while we transition between algebra
-- representations
module _ (R : CommRing ℓ) {A : Type ℓ}
  (0a 1a : A)
  (add mul : A → A → A)
  (inv : A → A)
  (e : ⟨ R ⟩ ≃ A)
  (p0 : e .fst (R .snd .0r) ≡ 0a)
  (p1 : e .fst (R .snd .1r) ≡ 1a)
  (p+ : ∀ x y → e .fst (R .snd ._+_ x y) ≡ add (e .fst x) (e .fst y))
  (p· : ∀ x y → e .fst (R .snd ._·_ x y) ≡ mul (e .fst x) (e .fst y))
  (pinv : ∀ x → e .fst (R .snd .-_ x) ≡ inv (e .fst x))
  where

  private
    module R = CommRingStr (R .snd)

    BaseΣ : Type (ℓ-suc ℓ)
    BaseΣ = Σ[ B ∈ Type ℓ ] B × B × (B → B → B) × (B → B → B) × (B → B)

    FamilyΣ : BaseΣ → Type ℓ
    FamilyΣ (B , u0 , u1 , a , m , i) = IsCommRing u0 u1 a m i

    inducedΣ : FamilyΣ (A , 0a , 1a , add , mul , inv)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel BaseΣ) (e , p0 , p1 , p+ , p· , pinv))
        R.isCommRing

  InducedCommRing : CommRing ℓ
  InducedCommRing .fst = A
  0r (InducedCommRing .snd) = 0a
  1r (InducedCommRing .snd) = 1a
  _+_ (InducedCommRing .snd) = add
  _·_ (InducedCommRing .snd) = mul
  - InducedCommRing .snd = inv
  isCommRing (InducedCommRing .snd) = inducedΣ

  InducedCommRingEquiv : CommRingEquiv R InducedCommRing
  fst InducedCommRingEquiv = e
  pres0 (snd InducedCommRingEquiv) = p0
  pres1 (snd InducedCommRingEquiv) = p1
  pres+ (snd InducedCommRingEquiv) = p+
  pres· (snd InducedCommRingEquiv) = p·
  pres- (snd InducedCommRingEquiv) = pinv

  InducedCommRingPath : R ≡ InducedCommRing
  InducedCommRingPath = CommRingPath _ _ .fst InducedCommRingEquiv
