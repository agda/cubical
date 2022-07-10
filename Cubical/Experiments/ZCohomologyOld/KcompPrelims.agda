{-# OPTIONS --safe #-}
module Cubical.Experiments.ZCohomologyOld.KcompPrelims where

open import Cubical.ZCohomology.Base
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Hopf
open S¹Hopf
-- open import Cubical.Homotopy.Freudenthal hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; map to trMap)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Int renaming (_+_ to +Int) hiding (_·_)
open import Cubical.Data.Nat hiding (_·_)
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
    ℓ : Level
    A : Type ℓ

{- We want to prove that Kn≃ΩKn+1. For this we use the map ϕ-}

-- Proof of Kₙ ≃ ∥ ΩSⁿ⁺¹ ∥ₙ for $n ≥ 2$
-- Entirely based on Cavallos proof of Freudenthal in Cubical.Homotopy.Freudenthal
module miniFreudenthal (n : HLevel) where
  σ : S₊ (2 + n) → typ (Ω (S₊∙ (3 + n)))
  σ a = merid a ∙ merid north ⁻¹

  S2+n = S₊ (2 + n)
  4n+2 = (2 + n) + (2 + n)

  module WC-S (p : north ≡ north) where
    P : (a b : S₊ (2 + n)) → Type₀
    P a b = σ b ≡ p → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)

    hLevelP : (a b : S₊ (2 + n)) → isOfHLevel 4n+2 (P a b)
    hLevelP _ _ = isOfHLevelΠ 4n+2 λ _ → isOfHLevelTrunc 4n+2

    leftFun : (a : S₊ (2 + n)) → P a north
    leftFun a r = ∣ a , (rCancel' (merid a) ∙ rCancel' (merid north) ⁻¹) ∙ r ∣

    rightFun : (b : S₊ (2 + n)) → P north b
    rightFun b r = ∣ b , r ∣

    funsAgree : leftFun north ≡ rightFun north
    funsAgree =
      funExt λ r → (λ i → ∣ north , rCancel' (rCancel' (merid north)) i ∙ r ∣)
                   ∙ λ i → ∣ north , lUnit r (~ i) ∣

    totalFun : (a b : S2+n) → P a b
    totalFun =  wedgeconFun (suc n) (suc n) hLevelP rightFun leftFun funsAgree

    leftId : (λ x → totalFun x north) ≡ leftFun
    leftId x i = wedgeconRight (suc n) (suc n) hLevelP rightFun leftFun funsAgree i x

  fwd : (p : north ≡ north) (a : S2+n)
    → hLevelTrunc 4n+2 (fiber σ p)
    → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
  fwd p a = trRec (isOfHLevelTrunc 4n+2) (uncurry (WC-S.totalFun p a))

  fwdnorth : (p : north ≡ north) → fwd p north ≡ idfun _
  fwdnorth p = funExt (trElim (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
                      λ p → refl)

  isEquivFwd : (p : north ≡ north) (a : S2+n) → isEquiv (fwd p a)
  isEquivFwd p =
    suspToPropElim (ptSn (suc n))
                   (λ _ → isPropIsEquiv _)
                   helper
    where
    helper : isEquiv (fwd p north)
    helper = subst isEquiv (sym (fwdnorth p)) (idIsEquiv _)

  interpolate : (a : S2+n)
          → PathP (λ i → S2+n → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
  interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

  Code : (y : Susp S2+n) → north ≡ y → Type₀
  Code north p = hLevelTrunc 4n+2 (fiber σ p)
  Code south q = hLevelTrunc 4n+2 (fiber merid q)
  Code (merid a i) p =
    Glue
      (hLevelTrunc 4n+2 (fiber (interpolate a i) p))
      (λ
        { (i = i0) → _ , (fwd p a , isEquivFwd p a)
        ; (i = i1) → _ , idEquiv _
        })

  encodeS : (y : S₊ (3 + n)) (p : north ≡ y) → Code y p
  encodeS y = J Code ∣ north , rCancel' (merid north) ∣

  encodeMerid : (a : S2+n) → encodeS south (merid a) ≡ ∣ a , refl ∣
  encodeMerid a =
    cong (transport (λ i → gluePath i))
      (funExt⁻ (funExt⁻ (WC-S.leftId refl) a) _ ∙ λ i → ∣ a , lem (rCancel' (merid a)) (rCancel' (merid north)) i ∣)
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 4n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

  contractCodeSouth : (p : north ≡ south) (c : Code south p) → encodeS south p ≡ c
  contractCodeSouth p =
    trElim
      (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
      (uncurry λ a →
        J (λ p r → encodeS south p ≡ ∣ a , r ∣) (encodeMerid a))

  isConnectedMerid : isConnectedFun 4n+2 (merid {A = S2+n})
  isConnectedMerid p = encodeS south p , contractCodeSouth p

  isConnectedσ : isConnectedFun 4n+2 σ
  isConnectedσ =
    transport (λ i → isConnectedFun 4n+2 (interpolate north (~ i))) isConnectedMerid

isConnectedσ-Sn : (n : ℕ) → isConnectedFun (4 + n) (miniFreudenthal.σ n)
isConnectedσ-Sn n =
  isConnectedFunSubtr _ n _
    (subst (λ x → isConnectedFun x (miniFreudenthal.σ n))
           helper
           (miniFreudenthal.isConnectedσ n))
  where
  helper : 2 + (n + (2 + n)) ≡ n + (4 + n)
  helper = cong suc (sym (+-suc n _)) ∙ sym (+-suc n _)

stabSpheres-n≥2 : (n : ℕ) → Iso (hLevelTrunc (4 + n) (S₊ (2 + n)))
                                  (hLevelTrunc (4 + n) (typ (Ω (S₊∙ (3 + n)))))
stabSpheres-n≥2 n = connectedTruncIso (4 + n) (miniFreudenthal.σ n) (isConnectedσ-Sn n)

--

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
    rotLemma : (r : S¹) → r · base ≡ r
    rotLemma base = refl
    rotLemma (loop i) = refl

sphereConnectedSpecCase : isConnected 4 (Susp (Susp S¹))
sphereConnectedSpecCase = sphereConnected 3

d-mapComp : Iso (fiber d-map base) (Path (S₊ 3) north north)
d-mapComp = compIso (IsoΣPathTransportPathΣ {B = HopfSuspS¹} _ _)
                     (congIso (invIso IsoS³TotalHopf))

is1Connected-dmap : isConnectedFun 3 d-map
is1Connected-dmap = toPropElim (λ _ → isPropIsOfHLevel 0)
                               (isConnectedRetractFromIso 3 d-mapComp
                                 (isOfHLevelRetractFromIso 0 (invIso (PathIdTruncIso 3))
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
Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS¹)) ΩS¹Isoℤ)
Iso-Kn-ΩKn+1 (suc zero) = compIso Iso∥ϕ₁∥ (invIso (PathIdTruncIso 3))
Iso-Kn-ΩKn+1 (suc (suc n)) = compIso (stabSpheres-n≥2 n)
                                     (invIso (PathIdTruncIso (4 + n)))
 where
  helper : n + (4 + n) ≡ 2 + (n + (2 + n))
  helper = +-suc n (3 + n) ∙ (λ i → suc (+-suc n (2 + n) i))
