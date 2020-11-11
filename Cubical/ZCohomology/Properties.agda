{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Properties where

open import Cubical.ZCohomology.Base
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Hopf
open import Cubical.Homotopy.Freudenthal hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; map to trMap) hiding (map2)
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)

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
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit

open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Bool
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.HITs.S3

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

{- Proof that Kₙ≃ΩKₙ₊₁ -}

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
Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS¹)) ΩS¹IsoInt)
Iso-Kn-ΩKn+1 (suc zero) = compIso Iso∥ϕ₁∥ (invIso (PathIdTruncIso 3))
Iso-Kn-ΩKn+1 (suc (suc n)) = compIso (stabSpheres-n≥2 n)
                                     (invIso (PathIdTruncIso (4 + n)))
 where
  helper : n + (4 + n) ≡ 2 + (n + (2 + n))
  helper = +-suc n (3 + n) ∙ (λ i → suc (+-suc n (2 + n) i))

------------------- Connectedness ---------------------
is2ConnectedKn : (n : ℕ) → isConnected 2 (coHomK (suc n))
is2ConnectedKn zero = ∣ ∣ base ∣ ∣
                    , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                        (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
                          (toPropElim (λ _ → isOfHLevelTrunc 2 _ _) refl))
is2ConnectedKn (suc n) = ∣ ∣ north ∣ ∣
                       , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                           (trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isOfHLevelTrunc 2 _ _))
                             (suspToPropElim (ptSn (suc n)) (λ _ → isOfHLevelTrunc 2 _ _) refl))

isConnectedKn : (n : ℕ) → isConnected (2 + n) (coHomK (suc n))
isConnectedKn n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (2 + n) 1)) (sphereConnected (suc n))

-- direct proof of connectedness of ΩKₙ₊₁ not relying on the equivalence ∥ a ≡ b ∥ₙ ≃ (∣ a ∣ₙ₊₁ ≡ ∣ b ∣ₙ₊₁)
isConnectedPathKn : (n : ℕ) (x y : (coHomK (suc n))) → isConnected (suc n) (x ≡ y)
isConnectedPathKn n =
  trElim (λ _ → isProp→isOfHLevelSuc (2 + n) (isPropΠ λ _ → isPropIsContr))
    (sphereElim _ (λ _ → isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr))
      λ y → isContrRetractOfConstFun
               {B = (hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n)))} ∣ refl ∣
                 (fun⁻ n y
                , trElim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
                         (J (λ y p → fun⁻ n y _ ≡ _) (funExt⁻ (fun⁻Id n) ∣ refl ∣))))
  where
  fun⁻ : (n : ℕ) → (y : coHomK (suc n)) →
         hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n))
      → hLevelTrunc (suc n) (∣ ptSn (suc n) ∣ ≡ y)
  fun⁻ n =
    trElim (λ _ → isOfHLevelΠ (3 + n) λ _ → isOfHLevelSuc (2 + n) (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n))))
      (sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelTrunc (suc n)) λ _ → ∣ refl ∣)

  fun⁻Id : (n : ℕ) → fun⁻ n ∣ ptSn (suc n) ∣ ≡ λ _ → ∣ refl ∣
  fun⁻Id zero = refl
  fun⁻Id (suc n) = refl

-------------------
-- Induction principles for cohomology groups (n ≥ 1)
-- If we want to show a proposition about some x : Hⁿ(A), it suffices to show it under the
-- assumption that x = ∣ f ∣₂ for some f : A → Kₙ and that f is pointed

coHomPointedElim : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → Type ℓ'}
                 → ((x : coHom (suc n) A) → isProp (B x))
                 → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
                 → (x : coHom (suc n) A) → B x
coHomPointedElim {ℓ' = ℓ'} {A = A} n a isprop indp =
  sElim (λ _ → isOfHLevelSuc 1 (isprop _))
         λ f → helper n isprop indp f (f a) refl
  where
  helper :  (n : ℕ) {B : coHom (suc n) A → Type ℓ'}
         → ((x : coHom (suc n) A) → isProp (B x))
         → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
         → (f : A → coHomK (suc n))
         → (x : coHomK (suc n))
         → f a ≡ x → B ∣ f ∣₂
  -- pattern matching a bit extra to avoid isOfHLevelPlus'
  helper zero isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ λ _ → isprop _))
           (toPropElim (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc zero) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ λ _ → isprop _))
           (suspToPropElim base (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc zero)) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc (suc n))) isprop ind f =
    trElim (λ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))


coHomPointedElim2 : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (x y : coHom (suc n) A) → B x y
coHomPointedElim2 {ℓ' = ℓ'} {A = A} n a isprop indp = sElim2 (λ _ _ → isOfHLevelSuc 1 (isprop _ _))
                                                   λ f g → helper n a isprop indp f g (f a) (g a) refl refl
  where
  helper : (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (f g : A → coHomK (suc n))
                 → (x y : coHomK (suc n))
                 → f a ≡ x → g a ≡ y
                 → B ∣ f ∣₂ ∣ g ∣₂
  helper zero a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ2 λ _ _ → isprop _ _))
          (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc zero) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 base (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc zero)) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc (suc n))) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))

{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                  (A : Type ℓ) →
                  (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₂
  module coHomRed+1 where
  helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
  helpLemma {C = C} = isoToPath (iso map1
                                     map2
                                     (λ b → linvPf b)
                                     (λ _  → refl))
    where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
    map1 f = map1' , refl
      module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)

    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
      where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
      helper (inl x) = refl
      helper (inr tt) = sym snd
coHomRed+1Equiv (suc zero) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK 1 , ∣ base ∣)} i ∥₂
coHomRed+1Equiv (suc (suc n)) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK (2 + n) , ∣ north ∣)} i ∥₂
