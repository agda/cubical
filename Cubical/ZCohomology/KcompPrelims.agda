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

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 zero x i = ∣ intLoop x i ∣
Kn→ΩKn+1 (suc zero) = trRec (isOfHLevelTrunc 4 ∣ north ∣ ∣ north ∣)
                             λ a i → ∣ ϕ base a i ∣
Kn→ΩKn+1 (suc (suc n)) = trRec (isOfHLevelTrunc (2 + (3 + n)) ∣ north ∣ ∣ north ∣)
                                λ a i → ∣ ϕ north a i ∣
private
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

d-mapComp : fiber d-map base ≡ Path (Susp (Susp S¹)) north north
d-mapComp = ΣPathTransport≡PathΣ {B = HopfSuspS¹} _ _ ∙ helper
  where
  helper : Path (Σ (Susp S¹) λ x → HopfSuspS¹ x) (north , base) (north , base) ≡ Path (Susp (Susp S¹)) north north
  helper = (λ i → (Path (S³≡TotalHopf (~ i))
                        (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
                        ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base)))))
         ∙ {!!}
           {-
           (λ i → Path (S³≡SuspSuspS¹ i) (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))-}

{-
  ----------------------------------- n = 1 -----------------------------------------------------

  {- We begin by stating some useful lemmas -}



  S³≡SuspSuspS¹ : S³ ≡ Susp (Susp S¹)
  S³≡SuspSuspS¹ = S³≡SuspS² ∙ λ i → Susp (S²≡SuspS¹ i)

  S3≡SuspSuspS¹ : S₊ 3 ≡ Susp (Susp S¹)
  S3≡SuspSuspS¹ = (λ i → Susp (Susp (Susp (ua Bool≃Susp⊥ (~ i))))) ∙ λ i → Susp (Susp (S¹≡SuspBool (~ i)))

  sphereConnectedSpecCase : isConnected 4 (Susp (Susp S¹))
  sphereConnectedSpecCase = transport (λ i → isConnected 4 (S3≡SuspSuspS¹ i)) (sphereConnected 3)


  {- We give the following map and show that its truncation is an equivalence -}

  d-map : typ (Ω ((Susp S¹) , north)) → S¹
  d-map p = subst HopfSuspS¹ p base



  d-mapComp : fiber d-map base ≡ Path (Susp (Susp S¹)) north north
  d-mapComp = ΣPathTransport≡PathΣ {B = HopfSuspS¹} _ _ ∙ helper
    where
    helper : Path (Σ (Susp S¹) λ x → HopfSuspS¹ x) (north , base) (north , base) ≡ Path (Susp (Susp S¹)) north north
    helper = (λ i → (Path (S³≡TotalHopf (~ i))
                          (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
                          ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))))) ∙
             (λ i → Path (S³≡SuspSuspS¹ i) (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))


  is1Connected-dmap : isConnectedFun 3 d-map
  is1Connected-dmap = toPropElim (λ s → isPropIsOfHLevel 0) (transport (λ j → isContr (∥ d-mapComp (~ j) ∥ 3))
                                      (transport (λ i →  isContr (PathΩ {A = Susp (Susp S¹)} {a = north} 3 i))
                                                 (refl , isOfHLevelSuc 1 (isOfHLevelSuc 0 sphereConnectedSpecCase) ∣ north ∣ ∣ north ∣ (λ _ → ∣ north ∣))))

  d-iso2 : Iso (hLevelTrunc 3 (typ (Ω (Susp S¹ , north)))) (hLevelTrunc 3 S¹)
  d-iso2 = connectedTruncIso _ d-map is1Connected-dmap

  {- We show that composing (λ a → ∣ ϕ base a ∣) and (λ x → ∣ d-map x ∣) gives us the identity function.  -}

  d-mapId2 : Iso.fun d-iso2 ∘ trMap (ϕ base) ≡ idfun (hLevelTrunc 3 S¹)
  d-mapId2 = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ a i → ∣ (d-mapId a i)∣))

  {- This means that (λ a → ∣ ϕ base a ∣) is an equivalence -}

  Iso∣ϕ-base∣ : Iso (hLevelTrunc 3 S¹) (hLevelTrunc 3 (typ (Ω (Susp S¹ , north))))
  Iso∣ϕ-base∣ = composesToId→Iso d-iso2 (trMap (ϕ base)) d-mapId2


  ---------------------------------
  -- We cheat when n = 1 and use J to prove the following lemmma.  There is an obvious dependent path between ϕ base and ϕ north. Since the first one is an iso, so is the other.
  -- So far this hasn't been an issue.


  pointFunIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ} {C : (A : Type ℓ) (a1 : A) → Type ℓ'} (p : A ≡ B) (a : A) (b : B) →
              (transport p a ≡ b) →
              (f : (A : Type ℓ) →
              (a1 : A) (a2 : hLevelTrunc 3 A)  → C A a1) →
              isIso (f A a) →
              isIso (f B b)
  pointFunIso {ℓ = ℓ}{A = A} {B = B} {C = C} =
           J (λ B p → (a : A) (b : B) →
                        (transport p a ≡ b) →
                        (f : (A : Type ℓ) →
                        (a1 : A) (a2 : hLevelTrunc 3 A)  → C A a1) →
                        isIso (f A a) →
                        isIso (f B b))
             λ a b trefl f is → transport (λ i → isIso (f A ((sym (transportRefl a) ∙ trefl) i))) is

  {- By pointFunIso, this gives that λ a → ∣ ϕ north a ∣ is an iso -}

  isIso∣ϕ∣ : isIso {A = hLevelTrunc 3 (S₊ 1)} {B = hLevelTrunc 3 (typ (Ω (S₊ 2 , north)))} (trMap (ϕ north))
  isIso∣ϕ∣ = pointFunIso {A = S¹} (λ i → S¹≡S1 (~ i)) base north refl (λ A a1 → trMap (ϕ a1)) ((Iso.inv Iso∣ϕ-base∣) , ((Iso.rightInv Iso∣ϕ-base∣) , (Iso.leftInv Iso∣ϕ-base∣)))

  Iso∣ϕ∣ : Iso (hLevelTrunc 3 (S₊ 1)) (hLevelTrunc 3 (typ (Ω (S₊ 2 , north))))
  Iso.fun Iso∣ϕ∣ = trMap (ϕ north)
  Iso.inv Iso∣ϕ∣ = isIso∣ϕ∣ .fst
  Iso.rightInv Iso∣ϕ∣ = isIso∣ϕ∣ .snd .fst
  Iso.leftInv Iso∣ϕ∣ = isIso∣ϕ∣ .snd .snd

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
