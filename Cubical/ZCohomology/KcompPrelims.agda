{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.KcompPrelims where

open import Cubical.ZCohomology.Base
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Hopf
open import Cubical.Homotopy.Freudenthal hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; rec to trRec ; map to trMap)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Int renaming (_+_ to +Int)
open import Cubical.Data.Nat
open import Cubical.Data.Unit

open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Prod.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Bool
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.HITs.S3

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


{- We want to prove that Kn≃ΩKn+1. For this we use the map ϕ-}

ϕ : (pt a : A) → typ (Ω (Susp A , north))
ϕ pt a = (merid a) ∙ sym (merid pt)

private
  Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
  Kn→ΩKn+1 zero x i = ∣ intLoop x i ∣
  Kn→ΩKn+1 (suc zero) = trRec (isOfHLevelTrunc 4 ∣ north ∣ ∣ north ∣)
                               λ a i → ∣ ϕ base a i ∣
  Kn→ΩKn+1 (suc (suc n)) = trRec (isOfHLevelTrunc (2 + (3 + n)) ∣ north ∣ ∣ north ∣)
                                  λ a i → ∣ ϕ north a i ∣

  d-map : typ (Ω ((Susp S¹) , north)) → S¹
  d-map p = subst HopfSuspS¹ p base

  d-mapId : (r : S¹) → d-map (ϕ base r) ≡ r
  d-mapId r = substComposite HopfSuspS¹ (merid r) (sym (merid base)) base ∙
              rotLemma r
    where
    rotLemma : (r : S¹) → rot r base ≡ r
    rotLemma base = refl
    rotLemma (loop i) = refl

sphereConnectedSpecCase : isConnected 4 (Susp (Susp S¹))
sphereConnectedSpecCase = sphereConnected 3

-- IsoS³TotalHopf

d-mapComp2 : Iso (fiber d-map base) (Path (S₊ 3) north north)
d-mapComp2 = compIso (IsoΣPathTransportPathΣ {B = HopfSuspS¹} _ _)
                     (congIso (invIso IsoS³TotalHopf))

isContrIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → isContr A → isContr B
isContrIso is cA = isContrRetract (Iso.inv is) (Iso.fun is) (Iso.rightInv is) cA

is1Connected-dmap : isConnectedFun 3 d-map
is1Connected-dmap = toPropElim (λ _ → isPropIsOfHLevel 0)
                               (isConnectedRetract 3
                                 (Iso.fun d-mapComp2)
                                 (Iso.inv d-mapComp2)
                                 (Iso.leftInv d-mapComp2)
                                 (isContrIso (PathIdTruncIso 3)
                                             contrHelper))
  where
  contrHelper : isContr (Path (∥ Susp (Susp S¹) ∥ 4) ∣ north ∣ ∣ north ∣)
  fst contrHelper = refl
  snd contrHelper = isOfHLevelPlus {n = 0} 2 (sphereConnected 3) ∣ north ∣ ∣ north ∣ refl

d-Iso : Iso (∥ Path (S₊ 2) north north ∥ 3) (coHomK 1)
d-Iso = connectedTruncIso _ d-map is1Connected-dmap

d-mapId2 : Iso.fun d-Iso ∘ trMap (ϕ base) ≡ idfun (coHomK 1)
d-mapId2 = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ a i → ∣ d-mapId a i ∣)

Iso∥ϕ₁∥ : Iso (coHomK 1) (∥ Path (S₊ 2) north north ∥ 3)
Iso∥ϕ₁∥ = composesToId→Iso d-Iso (trMap (ϕ base)) d-mapId2


Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS1)) ΩS¹IsoInt)
Iso-Kn-ΩKn+1 (suc zero) = compIso Iso∥ϕ₁∥ (invIso (PathIdTruncIso 3))
Iso-Kn-ΩKn+1 (suc (suc n)) = compIso (connectedTruncIso2 (4 + n) _ (ϕ north) (n , helper)
                                                                             (isConnectedσ (suc n) (sphereConnected _)))
                                     (invIso (PathIdTruncIso (4 + n)))
 where
  helper : n + (4 + n) ≡ 2 + (n + (2 + n))
  helper = +-suc n (3 + n) ∙ (λ i → suc (+-suc n (2 + n) i))


{-

---------------------------------------------------- Finishing up ---------------------------------

-- We need ΩTrunc. It appears to compute better when restated for this particular case --

decode-fun2 : (n : HLevel) → (x : A) → hLevelTrunc n (x ≡ x) → Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣
decode-fun2 zero x _ = isOfHLevelTrunc 1 _ _
decode-fun2 (suc n) x = trElim (λ _ → isOfHLevelPath' (suc n) (isOfHLevelTrunc (suc (suc n))) ∣ x ∣ ∣ x ∣) (cong ∣_∣)

funsAreSame : (n : HLevel) (x : A) (b : hLevelTrunc n (x ≡ x)) → (decode-fun2 n x b) ≡ Iso.inv (PathIdTruncIso n) b
funsAreSame zero x tt* = isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _ _ _
funsAreSame (suc zero) x = trElim (λ a → isOfHLevelPath 1 (isOfHLevelPath' 1 (isOfHLevelTrunc 2) ∣ x ∣ ∣ x ∣) _ _) λ p → refl
funsAreSame (suc (suc n)) x = trElim (λ a → isOfHLevelPath (2 + n) (isOfHLevelPath' (2 + n) (isOfHLevelTrunc (3 + n)) ∣ x ∣ ∣ x ∣) _ _) λ p → refl

decodeIso : (n : HLevel) (x : A) → Iso (hLevelTrunc n (x ≡ x)) (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣)
Iso.fun (decodeIso n x) = decode-fun2 n x
Iso.inv (decodeIso n x) = Iso.fun (PathIdTruncIso n) -- Iso.inv (PathIdTruncIso n)
Iso.rightInv (decodeIso n x) b = rInv n x b -- funsAreSame n x (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣ b) ∙ ΩTrunc.P-rinv ∣ x ∣ ∣ x ∣ b
  where
  rInv : (n : ℕ) (x : A) (b : Path (hLevelTrunc (suc n) A) _ _) → (decode-fun2 n x) (Iso.fun (PathIdTruncIso n) b) ≡ b
  rInv zero x b = isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _ _ _
  rInv (suc n) x b = funsAreSame (suc n) x (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣ b) ∙ ΩTrunc.P-rinv ∣ x ∣ ∣ x ∣ b
Iso.leftInv (decodeIso n x) b = lInv n x b
  where
  lInv : (n : ℕ) (x : _) (b : _) → Iso.fun (PathIdTruncIso n) (decode-fun2 n x b) ≡ b
  lInv zero x tt* = refl
  lInv (suc n) x b = cong (Iso.fun (PathIdTruncIso (suc n))) (funsAreSame (suc n) x b) ∙ ΩTrunc.P-linv ∣ x ∣ ∣ x ∣ b

Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso-Kn-ΩKn+1 zero = compIso isolooper (congIso (invIso (truncIdempotentIso _ isOfHLevelS1))) -- (congIso (truncIdempotentIso _ isOfHLevelS1))
Iso-Kn-ΩKn+1 (suc zero) = compIso Iso∣ϕ∣ (decodeIso _ north)
Iso-Kn-ΩKn+1 (suc (suc n)) = compIso (connectedTruncIso2 (4 + n) _ (ϕ north) (n , helper)
                                                                             (isConnectedσ (suc n) (sphereConnected _)))
                                     (decodeIso _ north)
  where
  helper : n + (4 + n) ≡ 2 + (n + (2 + n))
  helper = +-suc n (3 + n) ∙ (λ i → suc (+-suc n (2 + n) i))

mapId2 : (n : ℕ) →  Kn→ΩKn+1 n ≡ Iso.fun (Iso-Kn-ΩKn+1 n)
mapId2 zero = refl
mapId2 (suc zero) = funExt (trElim (λ x → isOfHLevelPath 3 (isOfHLevelTrunc 4 ∣ north ∣ ∣ north ∣) _ _) λ a → refl)
mapId2 (suc (suc n)) = funExt (trElim (λ x → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) ∣ north ∣ ∣ north ∣) _ _) λ a → refl)




-- Experiments with abstract definitions

Iso2-Kn-ΩKn+1 : (n : ℕ) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso.fun (Iso2-Kn-ΩKn+1 n) = Kn→ΩKn+1 n
Iso.inv (Iso2-Kn-ΩKn+1 n) = Iso.inv (Iso-Kn-ΩKn+1 n)
Iso.rightInv (Iso2-Kn-ΩKn+1 n) a = rinv
  where
  rinv : Kn→ΩKn+1 n (Iso.inv (Iso-Kn-ΩKn+1 n) a) ≡ a
  rinv = funExt⁻ (mapId2 n) _ ∙ Iso.rightInv (Iso-Kn-ΩKn+1 n) a
Iso.leftInv (Iso2-Kn-ΩKn+1 n) a = linv
  where
  linv : Iso.inv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n a) ≡ a
  linv = cong (Iso.inv (Iso-Kn-ΩKn+1 n)) (funExt⁻ (mapId2 n) a) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) a

--- even more abstract


absInv' : (n : ℕ) → typ (Ω (coHomK-ptd (2 + n))) → coHomK (1 + n)
absInv' n = Iso.inv (Iso-Kn-ΩKn+1 (1 + n))

absSect' : (n : ℕ) (a : typ (Ω (coHomK-ptd (2 + n)))) → Kn→ΩKn+1 (1 + n) (absInv' n a) ≡ a
absSect' n a = funExt⁻ (mapId2 (1 + n)) _ ∙ Iso.rightInv (Iso-Kn-ΩKn+1 (1 + n)) a

absRetr' : (n : ℕ) (a : coHomK (1 + n)) → absInv' n (Kn→ΩKn+1 (1 + n) a) ≡ a
absRetr' n a = cong (Iso.inv (Iso-Kn-ΩKn+1 (1 + n))) (funExt⁻ (mapId2 (1 + n)) a) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 (1 + n)) a


absInv : (n : ℕ) → typ (Ω (coHomK-ptd (1 + n))) → coHomK n
absInv zero = Iso.inv (Iso-Kn-ΩKn+1 zero)
absInv (suc n) = absInv' n

absSect : (n : ℕ) → section (Kn→ΩKn+1 n) (absInv n)
absSect zero a = funExt⁻ (mapId2 zero) (Iso.inv isolooper2 (Iso.inv (congIso (invIso (truncIdempotentIso _ isOfHLevelS1))) a)) ∙ Iso.rightInv (Iso-Kn-ΩKn+1 zero) a
absSect (suc n) = absSect' n

absRetr : (n : ℕ) → retract (Kn→ΩKn+1 n) (absInv n)
absRetr zero a = cong (Iso.inv (Iso-Kn-ΩKn+1 zero)) (funExt⁻ (mapId2 zero) a) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 zero) a
absRetr (suc n) = absRetr' n

Iso3-Kn-ΩKn+1 : (n : ℕ) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso.fun (Iso3-Kn-ΩKn+1 n) = Kn→ΩKn+1 n
Iso.inv (Iso3-Kn-ΩKn+1 n) = absInv n
Iso.rightInv (Iso3-Kn-ΩKn+1 n) = absSect n
Iso.leftInv (Iso3-Kn-ΩKn+1 n) = absRetr n

-}
