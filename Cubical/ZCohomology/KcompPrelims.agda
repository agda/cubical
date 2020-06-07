{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.KcompPrelims where

open import Cubical.ZCohomology.Base
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Hopf
open import Cubical.Homotopy.Freudenthal hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; map to trMap)

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
open import Cubical.Data.NatMinusTwo.Base

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

  {- To define the map for n=0 we use the λ k → loopᵏ map for S₊ 1. The loop is given by ϕ north south -}
private
  loop* : Path (S₊ 1) north north
  loop* = ϕ north south

looper : Int → Path (S₊ 1) north north
looper (pos zero) = refl
looper (pos (suc n)) = looper (pos n) ∙ loop*
looper (negsuc zero) = sym loop*
looper (negsuc (suc n)) = looper (negsuc n) ∙ sym loop*



private

  {- The map of Kn≃ΩKn+1 is given as follows. -}
  Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
  Kn→ΩKn+1 zero x = cong ∣_∣ (looper x)
  Kn→ΩKn+1 (suc n) = trRec (isOfHLevelTrunc (2 + (suc (suc n))) ∣ north ∣ ∣ north ∣)
                             λ a → cong ∣_∣ ((merid a) ∙ (sym (merid north)))

  {- We show that looper is a composition of intLoop with two other maps, all three being isos -}
  sndcomp : ΩS¹ → Path (Susp Bool) north north
  sndcomp = cong S¹→SuspBool

  thrdcomp : Path (Susp Bool) north north → Path (S₊ 1) north north
  thrdcomp = cong SuspBool→S1


  looper2 : Int → Path (S₊ 1) north north
  looper2 a = thrdcomp (sndcomp (intLoop a))

  looper≡looper2 : (x : Int) → looper x ≡ looper2 x
  looper≡looper2 (pos zero) = refl
  looper≡looper2 (pos (suc n)) =
         looper (pos n) ∙ loop*                                       ≡⟨ (λ i → looper≡looper2 (pos n) i ∙ congFunct SuspBool→S1 (merid false)  (sym (merid true)) (~ i)) ⟩
         looper2 (pos n) ∙ cong SuspBool→S1 (ϕ true false)           ≡⟨ sym (congFunct SuspBool→S1 (sndcomp (intLoop (pos n))) (ϕ true false)) ⟩
         cong SuspBool→S1 (sndcomp (intLoop (pos n)) ∙ ϕ true false) ≡⟨ cong thrdcomp (sym (congFunct S¹→SuspBool (intLoop (pos n)) loop)) ⟩
         looper2 (pos (suc n)) ∎
  looper≡looper2 (negsuc zero) =
         sym loop*                                                    ≡⟨ symDistr (merid south) (sym (merid north)) ⟩
         merid north ∙ sym (merid south)                              ≡⟨ sym (congFunct SuspBool→S1 (merid true) (sym (merid false))) ⟩
         cong SuspBool→S1 (merid true ∙ sym (merid false))           ≡⟨ cong thrdcomp (sym (symDistr (merid false) (sym (merid true)))) ⟩
         looper2 (negsuc zero) ∎
  looper≡looper2 (negsuc (suc n)) =
         looper (negsuc n) ∙ sym loop*                                                    ≡⟨ ((λ i → looper≡looper2 (negsuc n) i ∙ symDistr (merid south) (sym (merid north)) i)) ⟩
         looper2 (negsuc n) ∙ merid north ∙ sym (merid south)                             ≡⟨ cong (λ x → looper2 (negsuc n) ∙ x) (sym (congFunct SuspBool→S1 (merid true) (sym (merid false)))) ⟩
         looper2 (negsuc n) ∙ cong SuspBool→S1 (ϕ false true)                            ≡⟨ cong (λ x → looper2 (negsuc n) ∙ x) (cong thrdcomp (sym (symDistr (merid false) (sym (merid true))))) ⟩
         looper2 (negsuc n) ∙ cong SuspBool→S1 (sym (ϕ true false))                      ≡⟨ sym (congFunct SuspBool→S1 (sndcomp (intLoop (negsuc n))) (sym (ϕ true false))) ⟩
         thrdcomp (cong S¹→SuspBool (intLoop (negsuc n)) ∙ cong S¹→SuspBool (sym loop)) ≡⟨ cong thrdcomp (sym (congFunct S¹→SuspBool (intLoop (negsuc n)) (sym loop))) ⟩
         looper2 (negsuc (suc n)) ∎


  isolooper2 : Iso Int (Path (S₊ 1) north north)
  isolooper2 = compIso (iso intLoop winding (decodeEncode base) windingIntLoop)
                       (compIso iso2
                                iso1)
    where
    iso1 : Iso (Path (Susp Bool) north north) (Path (S₊ 1) north north)
    iso1 = congIso SuspBool≃S1

    iso2 : Iso ΩS¹ (Path (Susp Bool) north north)
    iso2 = congIso (isoToEquiv (iso S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹))

  isolooper : Iso Int (Path (S₊ 1) north north)
  Iso.fun isolooper = looper
  Iso.inv isolooper = Iso.inv isolooper2
  Iso.rightInv isolooper a = (looper≡looper2 (Iso.inv isolooper2 a)) ∙ Iso.rightInv isolooper2 a
  Iso.leftInv isolooper a = cong (Iso.inv isolooper2) (looper≡looper2 a) ∙ Iso.leftInv isolooper2 a


  {- We want to show that this map is an equivalence. n ≥ 2 follows from Freudenthal, and  -}

  {-
  We want to show that the function (looper : Int → S₊ 1) defined by λ k → loopᵏ is an equivalece. We already know that the corresponding function (intLoop : Int → S¹ is) an equivalence,
  so the idea is to show that when intLoop is transported along a suitable path S₊ 1 ≡ S¹ we get looper. Instead of using S₊ 1 straight away, we begin by showing this for the equivalent Susp Bool.
  -}



  ----------------------------------- n = 1 -----------------------------------------------------

  {- We begin by stating some useful lemmas -}



  S³≡SuspSuspS¹ : S³ ≡ Susp (Susp S¹)
  S³≡SuspSuspS¹ = S³≡SuspS² ∙ λ i → Susp (S²≡SuspS¹ i)

  S3≡SuspSuspS¹ : S₊ 3 ≡ Susp (Susp S¹)
  S3≡SuspSuspS¹ = (λ i → Susp (Susp (Susp (ua Bool≃Susp⊥ (~ i))))) ∙ λ i → Susp (Susp (S¹≡SuspBool (~ i)))

  sphereConnectedSpecCase : isHLevelConnected 4 (Susp (Susp S¹))
  sphereConnectedSpecCase = transport (λ i → isHLevelConnected 4 (S3≡SuspSuspS¹ i)) (sphereConnected 3)



  {- We give the following map and show that its truncation is an equivalence -}

  d-map : typ (Ω ((Susp S¹) , north)) → S¹
  d-map p = subst HopfSuspS¹ p base

  d-mapId : (r : S¹) → d-map (ϕ base r) ≡ r
  d-mapId r = substComposite HopfSuspS¹ (merid r) (sym (merid base)) base ∙
              rotLemma r
    where
    rotLemma : (r : S¹) → rot r base ≡ r
    rotLemma base = refl
    rotLemma (loop i) = refl

  d-mapComp : fiber d-map base ≡ Path (Susp (Susp S¹)) north north
  d-mapComp = ΣPathTransport≡PathΣ {B = HopfSuspS¹} _ _ ∙ helper
    where
    helper : Path (Σ (Susp S¹) λ x → HopfSuspS¹ x) (north , base) (north , base) ≡ Path (Susp (Susp S¹)) north north
    helper = (λ i → (Path (S³≡TotalHopf (~ i))
                          (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
                          ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))))) ∙
             (λ i → Path (S³≡SuspSuspS¹ i) (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))


  is1Connected-dmap : isHLevelConnectedFun 3 d-map
  is1Connected-dmap = toPropElim (λ s → isPropIsOfHLevel 0) (transport (λ j → isContr (∥ d-mapComp (~ j) ∥ ℕ→ℕ₋₂ 1))
                                      (transport (λ i →  isContr (PathΩ {A = Susp (Susp S¹)} {a = north} (ℕ→ℕ₋₂ 1) i))
                                                 (refl , isOfHLevelSuc 1 (isOfHLevelSuc 0 sphereConnectedSpecCase) ∣ north ∣ ∣ north ∣ (λ _ → ∣ north ∣))))


  d-iso2 : Iso (hLevelTrunc 3 (typ (Ω (Susp S¹ , north)))) (hLevelTrunc 3 S¹)
  d-iso2 = connectedTruncIso _ d-map is1Connected-dmap

  {- We show that composing (λ a → ∣ ϕ base a ∣) and (λ x → ∣ d-map x ∣) gives us the identity function.  -}

  d-mapId2 : Iso.fun d-iso2 ∘ trMap (ϕ base) ≡ idfun (hLevelTrunc 3 S¹)
  d-mapId2 = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ a → cong ∣_∣ (d-mapId a)))

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

decode-fun2 : (n : ℕ) → (x : A) → hLevelTrunc n (x ≡ x) → Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣
decode-fun2 zero x = trElim (λ _ → isOfHLevelPath 0 (∣ x ∣ , isOfHLevelTrunc 1 ∣ x ∣) ∣ x ∣ ∣ x ∣) (λ p i → ∣ p i ∣)
decode-fun2 (suc n) x = trElim (λ _ → isOfHLevelPath' (suc n) (isOfHLevelTrunc (suc (suc n))) ∣ x ∣ ∣ x ∣) (cong ∣_∣)

funsAreSame : (n : ℕ) (x : A) (b : hLevelTrunc n (x ≡ x)) → (decode-fun2 n x b) ≡ (ΩTrunc.decode-fun ∣ x ∣ ∣ x ∣ b)
funsAreSame zero x = trElim (λ a → isOfHLevelPath 0 (refl , (isOfHLevelSuc 1 (isOfHLevelTrunc 1) ∣ x ∣ ∣ x ∣ refl)) _ _) λ a → refl
funsAreSame (suc n) x = trElim (λ a → isOfHLevelPath _ (isOfHLevelPath' (suc n) (isOfHLevelTrunc (suc (suc n))) ∣ x ∣ ∣ x ∣) _ _) λ a → refl

decodeIso : (n : ℕ) (x : A) → Iso (hLevelTrunc n (x ≡ x)) (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣)
Iso.fun (decodeIso n x) = decode-fun2 n x
Iso.inv (decodeIso n x) = ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣
Iso.rightInv (decodeIso n x) b = funsAreSame n x (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣ b) ∙ ΩTrunc.P-rinv ∣ x ∣ ∣ x ∣ b
Iso.leftInv (decodeIso n x) b = cong (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣) (funsAreSame n x b) ∙ ΩTrunc.P-linv ∣ x ∣ ∣ x ∣ b

Iso-Kn-ΩKn+1 : (n : ℕ) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso-Kn-ΩKn+1 zero = compIso isolooper (congIso (truncIdempotent≃ _ isOfHLevelS1))
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

{- This version computes somewhat better -}

Iso2-Kn-ΩKn+1 : (n : ℕ) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso.fun (Iso2-Kn-ΩKn+1 n) = Kn→ΩKn+1 n
Iso.inv (Iso2-Kn-ΩKn+1 n) = Iso.inv (Iso-Kn-ΩKn+1 n)
Iso.rightInv (Iso2-Kn-ΩKn+1 n) a = rinv
  where
  abstract
    rinv : Kn→ΩKn+1 n (Iso.inv (Iso-Kn-ΩKn+1 n) a) ≡ a
    rinv = funExt⁻ (mapId2 n) _ ∙ Iso.rightInv (Iso-Kn-ΩKn+1 n) a
Iso.leftInv (Iso2-Kn-ΩKn+1 n) a = linv
  where
  abstract
    linv : Iso.inv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n a) ≡ a
    linv = cong (Iso.inv (Iso-Kn-ΩKn+1 n)) (funExt⁻ (mapId2 n) a) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) a
