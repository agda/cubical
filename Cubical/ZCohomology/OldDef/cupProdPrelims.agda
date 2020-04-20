{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.OldDef.cupProdPrelims where

open import Cubical.ZCohomology.OldDef.Base
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to +Int)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap)
open import Cubical.HITs.Hopf
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

isIso : (A → B) → Type _
isIso {A = A} {B = B} f = Σ[ g ∈ (B → A) ] section f g × retract f g

{- Some useful lemmas -- should probably be moved -}
congFunct : {a b c : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) → cong f (p ∙ q) ≡ cong f p ∙ cong f q
congFunct f p q i = hcomp (λ j → λ{(i = i0) → rUnit (cong f (p ∙ q)) (~ j) ;
                                    (i = i1) → cong f (rUnit p (~ j)) ∙ cong f q})
                          (cong f (p ∙ (λ k → q (k ∧ (~ i)))) ∙ cong f λ k → q ((~ i) ∨ k) )
                          -- 
symDistr : {a b c : A} (p : a ≡ b) (q : b ≡ c)  → sym (p ∙ q) ≡ sym q ∙ sym p
symDistr p q i = hcomp (λ j → λ{(i = i0) → rUnit (sym (p ∙ q)) (~ j)  ;
                                 (i = i1) → sym (lUnit q (~ j)) ∙ sym p})
                       (sym ((λ k → p (k ∨ i)) ∙ q) ∙ sym λ k → p (i ∧ k))

{- We want to prove that Kn≃ΩKn+1. For this we use the map ϕ-}


ϕ : (pt a : A) → typ (Ω (Susp A , north))
ϕ pt a = (merid a) ∙ sym (merid pt)

{- To define the map for n=0 we use the λ k → loopᵏ map for S₊ 1. The loop is given by ϕ south north -}


looper : Int → Path (S₊ 1) north north
looper (pos zero) = refl
looper (pos (suc n)) = looper (pos n) ∙ (ϕ south north)
looper (negsuc zero) = sym (ϕ south north)
looper (negsuc (suc n)) = looper (negsuc n) ∙ sym (ϕ south north)

{- The map of Kn≃ΩKn+1 is given as follows. -}
Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 zero x = cong ∣_∣ (looper x)
Kn→ΩKn+1 (suc n) = trElim (λ x → (isOfHLevelTrunc (2 + (suc (suc n))) ∣ north ∣ ∣ north ∣))
                           λ a → cong ∣_∣ ((merid a) ∙ (sym (merid north)))

{- We want to show that this map is an equivalence. n ≥ 2 follows from Freudenthal, and  -}

{-
We want to show that the function (looper : Int → S₊ 1) defined by λ k → loopᵏ is an equivalece. We already know that the corresponding function (intLoop : Int → S¹ is) an equivalence,
so the idea is to show that when intLoop is transported along a suitable path S₊ 1 ≡ S¹ we get looper. Instead of using S₊ 1 straight away, we begin by showing this for the equivalent Susp Bool.
-}

-- loop for Susp Bool --
loop* : Path (Susp Bool) north north
loop* = merid false ∙ sym (merid true)

-- the loop function --
intLoop* : Int → Path (Susp Bool) north north
intLoop* (pos zero) = refl
intLoop* (pos (suc n)) = intLoop* (pos n) ∙ loop*
intLoop* (negsuc zero) = sym loop*
intLoop* (negsuc (suc n)) = intLoop* (negsuc n) ∙ sym loop*

-- we show that the loop spaces agree --
loopSpId : ΩS¹ ≡ Path (Susp Bool) north north
loopSpId i = typ (Ω (S¹≡SuspBool i , transp ((λ j → S¹≡SuspBool (j ∧ i))) (~ i) base))

-- the transport map --
altMap2 : Int → Path (Susp Bool) north north
altMap2 n i = transport S¹≡SuspBool (intLoop n i)

-- We show that the transporting intLoop over S¹≡SuspBool gives intLoop* (modulo function extensionality) --
altMap≡intLoop*2 : (x : Int) → intLoop* x ≡ altMap2 x
altMap≡intLoop*2 (pos zero) = refl
altMap≡intLoop*2 (pos (suc n)) = (λ i → (altMap≡intLoop*2 (pos n) i) ∙ loop*) ∙
                                 sym (helper n)

  where
  helper : (n : ℕ) → altMap2 (pos (suc n)) ≡ altMap2 (pos n) ∙ loop*
  helper zero = (λ i j → transport S¹≡SuspBool (lUnit loop (~ i) j)) ∙
                (λ i j → transport S¹≡SuspBool (loop j)) ∙
                (λ i j → transportRefl ((merid false ∙ (sym (merid true))) j) i ) ∙
                lUnit loop*
  helper (suc n) = anotherHelper n ∙
                   (λ i → altMap2 (pos (suc n)) ∙ helper zero i) ∙
                   (λ i → altMap2 (pos (suc n)) ∙ lUnit loop* (~ i))
    where
    anotherHelper : (n : ℕ) → altMap2 (pos (suc (suc n))) ≡ altMap2 (pos (suc n)) ∙ altMap2 (pos 1)
    anotherHelper n = ((λ i j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ loop) j))) ∙
                         rUnit (λ j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ loop) j) ) ∙
                         (λ i → (λ j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ λ k → loop (k ∧ (~ i))) j)) ∙ λ j → transport S¹≡SuspBool (loop (j ∨ (~ i)))) ∙
                         (λ i → (λ j → transport S¹≡SuspBool (rUnit (intLoop (pos (suc n))) (~ i) j)) ∙ λ j → transport S¹≡SuspBool ((lUnit loop i) j))

altMap≡intLoop*2 (negsuc zero) = sym ((λ i j → transport S¹≡SuspBool (loop (~ j))) ∙
                                     λ  i j → transportRefl (loop* (~ j)) i )
altMap≡intLoop*2 (negsuc (suc n)) = helper n
  where
  altMapneg1 : altMap2 (negsuc zero) ≡ sym (loop*)
  altMapneg1 i j = transportRefl (loop* (~ j)) i

  anotherHelper : (n : ℕ) → altMap2 (negsuc (suc n)) ≡ altMap2 (negsuc n) ∙ altMap2 (negsuc zero)
  anotherHelper n = ((λ i → rUnit (λ j → (transport S¹≡SuspBool ((intLoop (negsuc n) ∙ sym loop) j))) i)) ∙
                       ((λ i → (λ j → transport S¹≡SuspBool ((intLoop (negsuc n) ∙ (λ k → loop ((~ k) ∨ i))) j)) ∙ λ j → transport S¹≡SuspBool (loop ((~ j) ∧ i)))) ∙
                       (λ i → ((λ j → transport S¹≡SuspBool (rUnit (intLoop (negsuc n)) (~ i) j))) ∙ altMap2 (negsuc zero))

  helper : (n : ℕ) → intLoop* (negsuc n) ∙ (sym loop*) ≡ altMap2 (negsuc (suc n))
  helper zero = (λ i → altMapneg1 (~ i) ∙ altMapneg1 (~ i)) ∙ sym (anotherHelper zero)
  helper (suc n) = (λ i → (helper n i) ∙ altMapneg1 (~ i) ) ∙
                   sym (anotherHelper (suc n))


isIsoAltMap2 : Iso Int (Path (Susp Bool) north north)
isIsoAltMap2 = compIso iso1 iso2
  where
  iso1 : Iso Int ΩS¹
  Iso.fun iso1 = intLoop
  Iso.inv iso1 = winding
  Iso.rightInv iso1 = decodeEncode base
  Iso.leftInv iso1 = windingIntLoop
  iso2 : Iso ΩS¹ (Path (Susp Bool) north north)
  Iso.fun iso2 = cong (transport S¹≡SuspBool) -- λ x i → transport S¹≡SuspBool (x i)
  Iso.inv iso2 = Iso.inv (congIso S¹≃SuspBool)
  Iso.rightInv iso2 b = (λ i → cong (funExt (λ z → transportRefl (S¹→SuspBool z)) i) (Iso.inv (congIso {x = base} {y = base} S¹≃SuspBool) b)) ∙
                        Iso.rightInv (congIso {x = base} {y = base} S¹≃SuspBool) b
  Iso.leftInv iso2 b = (λ i → Iso.inv (congIso S¹≃SuspBool) (cong (funExt (λ z → transportRefl (S¹→SuspBool z)) i) b)) ∙
                        Iso.leftInv (congIso {x = base} {y = base} S¹≃SuspBool) b

{- We have that the transported map is an equivalence -}
mapIsEquiv : isEquiv altMap2
mapIsEquiv = compEquiv (intLoop , (isoToIsEquiv (iso intLoop winding (decodeEncode base) windingIntLoop))) ((λ x i → transport S¹≡SuspBool (x i)) , helper) .snd
  where
  helper : isEquiv {A = ΩS¹} {B = _≡_ {A = Susp Bool} north north} (λ x i → transport S¹≡SuspBool (x i))
  helper = congEquiv (transport S¹≡SuspBool , helper3) .snd
    where
    helper2 : transport S¹≡SuspBool ≡ S¹→SuspBool
    helper2 = funExt λ z → transportRefl (S¹→SuspBool z)
    helper3 : isEquiv (transport S¹≡SuspBool )
    helper3 = transport (λ i → isEquiv (helper2 (~ i))) (S¹≃SuspBool .snd)

{- From this we get that intLoop* is an equivalence-}
intLoop*Equiv : isEquiv intLoop*
intLoop*Equiv = transport (λ i → isEquiv (funExt (altMap≡intLoop*2) (~ i))) mapIsEquiv

{- We now only need to work with Susp Bool and S₊ 1. We transport intLoop* along a path S1≡SuspBool and show that this gives us looper. -}
SuspBool→S1 : Susp Bool → S₊ 1
SuspBool→S1 north = north
SuspBool→S1 south = south
SuspBool→S1 (merid false i) = merid north i
SuspBool→S1 (merid true i) = merid south i

S1→SuspBool : S₊ 1 → Susp Bool
S1→SuspBool north = north
S1→SuspBool south = south
S1→SuspBool (merid north i) = merid false i
S1→SuspBool (merid south i) = merid true i

{- We need to spell out the trivial equivalence S1≃SuspBool. Of course it's important to make sure that we choose the right version of it. -}
S1≃SuspBool : Susp Bool ≃ S₊ 1
S1≃SuspBool = isoToEquiv (iso SuspBool→S1 S1→SuspBool  retrHelper sectHelper)
  where
  sectHelper : section S1→SuspBool SuspBool→S1
  sectHelper north = refl
  sectHelper south = refl
  sectHelper (merid false i) = refl
  sectHelper (merid true i) = refl

  retrHelper : retract S1→SuspBool SuspBool→S1
  retrHelper north = refl
  retrHelper south = refl
  retrHelper (merid north i) = refl
  retrHelper (merid south i) = refl

{- We show that transporting intLoop* along (ua S1≃SuspBool) gives us looper (again, modulo function extensionality) -}
looperIntoBool : (x : Int) → looper x ≡ λ i → transport ((ua (S1≃SuspBool))) (intLoop* x i)
looperIntoBool (pos zero) = refl
looperIntoBool (pos (suc n)) = (λ j → looperIntoBool (pos n) j ∙ merid north ∙ sym (merid south)) ∙
                               (λ j → (λ i → transportRefl (SuspBool→S1 (intLoop* (pos n) i)) j ) ∙ merid north ∙ sym (merid south)) ∙
                               (λ j → cong SuspBool→S1 (intLoop* (pos n)) ∙ congFunct SuspBool→S1 (merid false) (sym (merid true)) (~ j)) ∙
                               sym (congFunct SuspBool→S1 (intLoop* (pos n)) loop*) ∙
                               λ j i → transportRefl (SuspBool→S1 ((intLoop* (pos n) ∙ loop*) i)) (~ j)  
looperIntoBool (negsuc zero) = symDistr (merid north) (sym (merid south))  ∙
                               sym (congFunct SuspBool→S1 (merid true) (sym (merid false))) ∙ 
                               (λ j → cong SuspBool→S1 (merid true ∙ sym (merid false))) ∙
                               (λ j → cong SuspBool→S1 (symDistr (merid false) (sym (merid true)) (~ j))) ∙
                               λ j i → transportRefl (SuspBool→S1 (loop* (~ i))) (~ j)
looperIntoBool (negsuc (suc n)) = (λ i → looperIntoBool (negsuc n) i ∙ sym ((merid north) ∙ (sym (merid south))) ) ∙
                                  (λ i → looperIntoBool (negsuc n) i1 ∙ symDistr (merid north) (sym (merid south)) i) ∙
                                  (λ j → (λ i → transportRefl (SuspBool→S1 (intLoop* (negsuc n) i)) j) ∙ merid south ∙ sym (merid north)) ∙
                                  (λ j → cong SuspBool→S1 (intLoop* (negsuc n)) ∙ congFunct SuspBool→S1 (merid true) (sym (merid false)) (~ j)) ∙
                                  ((λ j → cong SuspBool→S1 (intLoop* (negsuc n)) ∙ cong SuspBool→S1 (symDistr (merid false) (sym (merid true)) (~ j)))) ∙
                                  sym (congFunct SuspBool→S1 (intLoop* (negsuc n)) (sym loop*)) ∙
                                  λ j i → transportRefl (SuspBool→S1 ((intLoop* (negsuc n) ∙ sym loop*) i)) (~ j)

{- From this, we can finally deduce that looper is an equivalence-}
isEquivLooper : isEquiv looper
isEquivLooper = transport (λ i → isEquiv (funExt (looperIntoBool) (~ i))) isEquivTranspIntLoop
  where
  isEquivTranspIntLoop : isEquiv λ x → cong (transport ((ua (S1≃SuspBool)))) (intLoop* x)
  isEquivTranspIntLoop = compEquiv (intLoop* , intLoop*Equiv)
                                   (cong (transport (ua S1≃SuspBool)) ,
                                     congEquiv (transport (ua S1≃SuspBool) ,
                                               transportEquiv (ua S1≃SuspBool) .snd) .snd) .snd

isIsoLooper : Iso Int (Path (S₊ 1) north north)
isIsoLooper = compIso isIsoAltMap2 (congIso S1≃SuspBool)
  where
  iso2 : Iso (Path (Susp Bool) north north) (Path (S₊ 1) north north)
  iso2 = congIso S1≃SuspBool

isIsoLooperId : (n : ℕ) → Iso.fun isIsoLooper (pos (suc n)) ≡ Iso.fun isIsoLooper (pos n) ∙ Iso.fun isIsoLooper (pos 1)
isIsoLooperId n  = (λ i → Iso.fun (congIso S1≃SuspBool) (congFunct (transport S¹≡SuspBool) (intLoop (pos n)) loop i)) ∙
                   congFunct (S1≃SuspBool .fst) (cong (transport S¹≡SuspBool) (intLoop (pos n))) (cong (transport S¹≡SuspBool) loop) ∙
                   (λ i → cong (S1≃SuspBool .fst) (cong (transport S¹≡SuspBool) (intLoop (pos n))) ∙ cong (S1≃SuspBool .fst) (cong (transport S¹≡SuspBool) (lUnit loop i)))

helper : (x : Int) → looper x ≡ Iso.fun isIsoLooper x
helper (pos zero) = refl
helper (pos (suc zero)) = sym (lUnit (ϕ south north)) ∙ (λ i → merid north ∙ sym (merid south)) ∙ {!!} ∙ {!Iso.fun isIsoLooper (pos (suc zero))!} ∙ λ i → Iso.fun (congIso S1≃SuspBool) (cong (transport S¹≡SuspBool) (lUnit loop i))
helper (pos (suc (suc n))) = {!!} ∙ {!!}
helper (negsuc n) = {!!}
  where
  helper2 : (x : SuspBool) → SuspBool→S1 ≡ {!!} 
  helper2 = {!!}

isIsoLooper2 : Iso Int (Path (S₊ 1) north north)
Iso.fun isIsoLooper2 = looper
Iso.inv isIsoLooper2 = Iso.inv isIsoLooper
Iso.rightInv isIsoLooper2 b = {!SuspBool→S1
    (transp (λ i₂ → SuspBool) i0 (S¹→SuspBool (intLoop x i₁)))!} ∙ Iso.rightInv isIsoLooper b
Iso.leftInv isIsoLooper2 b = {!!} ∙ Iso.leftInv isIsoLooper b

-- ----------------------------------- n = 1 -----------------------------------------------------

-- {- We begin by stating some useful lemmas -}

-- sphereConnectedSpecCase : isHLevelConnected 4 (Susp (Susp S¹)) -- is- 2 -ConnectedType (Susp (Susp S¹))
-- sphereConnectedSpecCase = transport (λ i → isHLevelConnected 4 (helper i)) (sphereConnected 3)
--   where
--   helper : S₊ 3 ≡ Susp (Susp S¹)
--   helper = (λ i → Susp (Susp (Susp (ua Bool≃Susp⊥ (~ i))))) ∙ λ i → Susp (Susp (S¹≡SuspBool (~ i)))

-- S¹≡S1 : S₊ 1 ≡ S¹
-- S¹≡S1 = (λ i → Susp (ua (Bool≃Susp⊥) (~ i))) ∙ sym S¹≡SuspBool

-- S³≡SuspSuspS¹ : S³ ≡ Susp (Susp S¹)
-- S³≡SuspSuspS¹ = S³≡SuspS² ∙ λ i → Susp (S²≡SuspS¹ i)

-- isSetS1 : isSet (Path (S₊ 1) north north)
-- isSetS1 = transport (λ i → isSet (helper i)) isSetInt 
--   where
--   helper : Int ≡ (Path (S₊ 1) north north)
--   helper = sym ΩS¹≡Int ∙
--            (λ i → typ (Ω (S¹≡SuspBool i , transport (λ j → S¹≡SuspBool (j ∧ i)) base))) ∙
--            (λ i → typ (Ω (ua S1≃SuspBool i , transport (λ j → ua S1≃SuspBool (i ∧ j)) north))) 

-- isEquivHelper2 : isOfHLevel 3 A → isEquiv {B = ∥ A ∥ 1} ∣_∣
-- isEquivHelper2  ofHlevl =
--                isoToIsEquiv (iso ∣_∣
--                                  (trElim (λ _ → ofHlevl) (λ a → a))
--                                  (trElim {B = λ b → ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ ≡ b}
--                                          (λ b → isOfHLevelSuc 3 (isOfHLevelTrunc 3)
--                                                                  ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ b)
--                                          λ a → refl)
--                                  λ b → refl)

-- isEquivHelper : {a b : A} → isOfHLevel 3 A → isEquiv {B = Path (∥ A ∥ 1) ∣ a ∣ ∣ b ∣ } (cong ∣_∣)
-- isEquivHelper {A = A} {a = a} {b = b} ofHlevl = congEquiv (∣_∣ , isEquivHelper2 ofHlevl) .snd

-- {- We give the following map and show that it is an equivalence -}

-- d-map : typ (Ω ((Susp S¹) , north)) → S¹ 
-- d-map p = subst HopfSuspS¹ p base

-- d-mapId : (r : S¹) → d-map (ϕ base r) ≡ r
-- d-mapId r = substComposite HopfSuspS¹ (merid r) (sym (merid base)) base ∙
--             rotLemma r
--   where
--   rotLemma : (r : S¹) → rot r base ≡ r
--   rotLemma base = refl
--   rotLemma (loop i) = refl

-- d-mapComp : fiber d-map base ≡ Path (Susp (Susp S¹)) north north
-- d-mapComp = sym (pathSigma≡sigmaPath {B = HopfSuspS¹} _ _) ∙ helper 
--   where
--   helper : Path (Σ (Susp S¹) λ x → HopfSuspS¹ x) (north , base) (north , base) ≡ Path (Susp (Susp S¹)) north north
--   helper = (λ i → (_≡_ {A = S³≡TotalHopf (~ i)}
--                         (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
--                         ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))))) ∙
--            (λ i → _≡_ {A = S³} base base) ∙
--            (λ i → _≡_ {A = S³≡SuspSuspS¹ i} (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))


-- is1Connected-dmap : isHLevelConnectedFun 3 d-map
-- is1Connected-dmap = toSetelim (λ s → isPropIsOfHLevel 0) (transport (λ j → isContr (∥ d-mapComp (~ j) ∥ ℕ→ℕ₋₂ 1))
--                                     (transport (λ i →  isContr (PathΩ {A = Susp (Susp S¹)} {a = north} (ℕ→ℕ₋₂ 1) i))
--                                                (refl , isOfHLevelSuc 1 (isOfHLevelSuc 0 sphereConnectedSpecCase) ∣ north ∣ ∣ north ∣ (λ _ → ∣ north ∣))))

-- d-equiv : isEquiv {A = ∥  typ (Ω (Susp S¹ , north)) ∥ (ℕ→ℕ₋₂ 1)} {B = ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (trElim (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣ )
-- d-equiv = connectedTruncEquiv _ d-map is1Connected-dmap .snd

-- d-iso2 : Iso (∥  typ (Ω (Susp S¹ , north)) ∥ (ℕ→ℕ₋₂ 1)) (∥ S¹ ∥ (ℕ→ℕ₋₂ 1))
-- Iso.fun d-iso2 = trMap d-map
-- Iso.inv d-iso2 = Iso.inv (connectedTruncIso _ d-map is1Connected-dmap)
-- Iso.rightInv d-iso2 = Iso.rightInv (connectedTruncIso _ d-map is1Connected-dmap)
-- Iso.leftInv d-iso2 = Iso.leftInv (connectedTruncIso _ d-map is1Connected-dmap)

-- d-iso : isIso {A = ∥  typ (Ω (Susp S¹ , north)) ∥ (ℕ→ℕ₋₂ 1)} {B = ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (trElim (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣ ) 
-- d-iso = (Iso.inv (connectedTruncIso _ d-map is1Connected-dmap)) , (Iso.rightInv (connectedTruncIso _ d-map is1Connected-dmap)
--                                                                 , Iso.leftInv (connectedTruncIso _ d-map is1Connected-dmap))

-- {- We show that composing (λ a → ∣ ϕ base a ∣) and (λ x → ∣ d-map x ∣) gives us the identity function.  -}

-- d-mapId2 : (λ (x : ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)) → (trElim {n = 3} {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
--                                              (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣) x)) ≡ λ x → x
-- d-mapId2 = funExt (trElim (λ x → isOfHLevelSuc 2 (isOfHLevelTrunc 3 ((trElim {n = 3}
--                                                                               {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)}
--                                                                               (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
--                                                                               (trElim (λ _ → isOfHLevelTrunc 3)
--                                                                                       (λ a → ∣ ϕ base a ∣) x)) x))
--                           λ a i → ∣ d-mapId a i ∣)

-- {- This means that (λ a → ∣ ϕ base a ∣) is an equivalence -}
-- isEquiv∣ϕ-base∣ : isEquiv {A = ∥ S¹ ∥ ℕ→ℕ₋₂ 1} (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣))
-- isEquiv∣ϕ-base∣ = composesToId→Equiv (trElim {n = 3} {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
--                           (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣))
--                           d-mapId2
--                           d-equiv

-- isIso∣ϕ-base∣ : Iso (∥ S¹ ∥ (ℕ→ℕ₋₂ 1)) (∥ typ (Ω (Susp S¹ , north)) ∥ ℕ→ℕ₋₂ 1)
-- isIso∣ϕ-base∣ = composesToId→Iso d-iso2 (trMap (ϕ base)) d-mapId2


-- ---------------------------------
-- -- We cheat when n = 1 and use J to prove the following lemmma.  There is an obvious dependent path between ϕ base and ϕ north. Since the first one is an equivalence, so is the other.
-- --


-- pointFunIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ} {C : (A : Type ℓ) (a1 : A) → Type ℓ'} (p : A ≡ B) (a : A) (b : B) →
--             (transport p a ≡ b) →
--             (f : (A : Type ℓ) →
--             (a1 : A) (a2 : ∥ A ∥ 1)  → C A a1) →
--             isIso (f A a) →
--             isIso (f B b)
-- pointFunIso {ℓ = ℓ}{A = A} {B = B} {C = C} =
--          J (λ B p → (a : A) (b : B) →
--                       (transport p a ≡ b) →
--                       (f : (A : Type ℓ) →
--                       (a1 : A) (a2 : ∥ A ∥ 1)  → C A a1) →
--                       isIso (f A a) →
--                       isIso (f B b))
--            λ a b trefl f is → transport (λ i → isIso (f A ((sym (transportRefl a) ∙ trefl) i))) is

-- {- By pointFunEquiv, this gives that λ a → ∣ ϕ north a ∣ is an equivalence. -}

-- isIso∣ϕ∣ : isIso {A = ∥ S₊ 1 ∥ 1} {B = ∥ typ (Ω (S₊ 2 , north)) ∥ 1} (trMap (ϕ north)) --(trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ north a ∣))
-- isIso∣ϕ∣ = pointFunIso {A = S¹} (λ i → S¹≡S1 (~ i)) base north refl (λ A a1 → trMap (ϕ a1)) ((Iso.inv isIso∣ϕ-base∣) , ((Iso.rightInv isIso∣ϕ-base∣) , (Iso.leftInv isIso∣ϕ-base∣)))

-- Iso∣ϕ∣ : Iso (∥ S₊ 1 ∥ 1) (∥ typ (Ω (S₊ 2 , north)) ∥ 1)
-- Iso.fun Iso∣ϕ∣ = trMap (ϕ north)
-- Iso.inv Iso∣ϕ∣ = isIso∣ϕ∣ .fst
-- Iso.rightInv Iso∣ϕ∣ = proj₁ (isIso∣ϕ∣ .snd)
-- Iso.leftInv Iso∣ϕ∣ = proj₂ (isIso∣ϕ∣ .snd)

-- -- isEquiv∣ϕ∣ : isEquiv {A = ∥ S₊ 1 ∥ 1} {B = ∥ typ (Ω (S₊ 2 , north)) ∥ 1} (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ north a ∣))
-- -- isEquiv∣ϕ∣ = pointFunEquiv {A = S¹} (λ i → S¹≡S1 (~ i)) base north refl (λ A a1 → trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ a1 a ∣)) isEquiv∣ϕ-base∣

-- -- ---------------------------------------------------- Finishing up ---------------------------------



-- decode-fun2 : (n : ℕ) → (x : A) → hLevelTrunc n (x ≡ x) → Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣
-- decode-fun2 zero x = trElim (λ _ → isOfHLevelPath 0 (∣ x ∣ , isOfHLevelTrunc 1 ∣ x ∣) ∣ x ∣ ∣ x ∣) (λ p i → ∣ p i ∣)
-- decode-fun2 (suc n) x = trElim (λ _ → isOfHLevelPath' (suc n) (isOfHLevelTrunc (suc (suc n))) ∣ x ∣ ∣ x ∣) (cong ∣_∣)

-- r : {n : ℕ} (x : A) → (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣)  --   (u : ∥ A ∥ (suc₋₂ m)) → P u u
-- r x = (λ _ → ∣ x ∣)

-- -- r : {m : ℕ₋₂} (u : ∥ B ∥ (suc₋₂ m)) → P u u
-- -- r = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

-- funsAreSame : (n : ℕ) (x : A) (b : hLevelTrunc n (x ≡ x)) → (decode-fun2 n x b) ≡ (ΩTrunc.decode-fun ∣ x ∣ ∣ x ∣ b)
-- funsAreSame zero x = trElim (λ a → isOfHLevelPath 0 (refl , (isOfHLevelSuc 1 (isOfHLevelTrunc 1) ∣ x ∣ ∣ x ∣ refl)) _ _) λ a → refl
-- funsAreSame (suc n) x = trElim (λ a → isOfHLevelPath _ (isOfHLevelPath' (suc n) (isOfHLevelTrunc (suc (suc n))) ∣ x ∣ ∣ x ∣) _ _) λ a → refl

-- decodeIso : (n : ℕ) → (x : A) → Iso (hLevelTrunc n (x ≡ x)) (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣)
-- Iso.fun (decodeIso n x) = decode-fun2 n x
-- Iso.inv (decodeIso n x) = ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣
-- Iso.rightInv (decodeIso n x) b = funExt⁻ (funExt (funsAreSame n x)) (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣ b)   ∙ ΩTrunc.P-rinv ∣ x ∣ ∣ x ∣ b
-- Iso.leftInv (decodeIso n x) b = cong (ΩTrunc.encode-fun ∣ x ∣ ∣ x ∣) (funsAreSame n x b) ∙ ΩTrunc.P-linv ∣ x ∣ ∣ x ∣ b

-- encode-fun2 : (n : ℕ) → (x y : A) → Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ y ∣ → hLevelTrunc n (x ≡ y)
-- encode-fun2 x y p = transport (λ i → {!!}) {!!}

-- -- encode-fun2 : {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → x ≡ y → P x y
-- -- encode-fun2 x y p = transport (λ i → P x (p i)) (r x)



-- Kn→ΩKn+1Sucn : (n : ℕ) → Kn→ΩKn+1 (suc n) ≡ λ x → decode-fun2 _ north (trElim (λ _ → isOfHLevelTrunc (3 + n)) (λ a → ∣ ϕ north a ∣) x)
-- Kn→ΩKn+1Sucn n = funExt (trElim (λ x → isOfHLevelSuc (2 + n) (isOfHLevelTrunc (4 + n) ∣ north ∣ ∣ north ∣ _ _))
--                                  λ a → refl)


-- Kn≃ΩKn+1 : (n : ℕ) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
-- -- n = 0
-- Kn≃ΩKn+1 zero = compIso {!!} (congIso (isoToEquiv (iso {!!} {!!} {!!} {!!})))
-- --- n = 1
-- Kn≃ΩKn+1 (suc zero) = compIso Iso∣ϕ∣ (decodeIso _ north)
-- --- n = 2
-- Kn≃ΩKn+1 (suc (suc n)) = compIso (connectedTruncIso2 (4 + n) _ (ϕ north) (n , (λ i → suc (suc (suc (+-suc n n (~ i))))) ∙
--                                                                                (λ i → suc (suc (+-suc n (suc n) ((~ i))))))
--                                                                           (isConnectedσ (suc n) (sphereConnected _)))
--                                  (decodeIso _ north)



-- -- {- For n ≥ 1, we rewrite our function as the composition below. -}
-- -- Kn→ΩKn+1Sucn : (n : ℕ) → Kn→ΩKn+1 (suc n) ≡ λ x → truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (3 + n)) (λ a → ∣ ϕ north a ∣) x)
-- -- Kn→ΩKn+1Sucn n = funExt (trElim (λ x → isOfHLevelSuc (suc (suc n))
-- --                                                        ((isOfHLevelTrunc ( 2 + (suc (suc n))) ∣ north ∣ ∣ north ∣)
-- --                                                                      (Kn→ΩKn+1 (suc n) x)
-- --                                                                      (truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (2 + (suc n))) (λ a → ∣ ϕ north a ∣) x))))
-- --                                  λ a → refl)




-- -- -- {- For n ≥ 1, we rewrite our function as the composition below. -}
-- -- -- Kn→ΩKn+1Sucn : (n : ℕ) → Kn→ΩKn+1 (suc n) ≡ λ x → truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (3 + n)) (λ a → ∣ ϕ north a ∣) x)
-- -- -- Kn→ΩKn+1Sucn n = funExt (trElim (λ x → isOfHLevelSuc (suc (suc n))
-- -- --                                                        ((isOfHLevelTrunc ( 2 + (suc (suc n))) ∣ north ∣ ∣ north ∣)
-- -- --                                                                      (Kn→ΩKn+1 (suc n) x)
-- -- --                                                                      (truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (2 + (suc n))) (λ a → ∣ ϕ north a ∣) x))))
-- -- --                                  λ a → refl)


-- -- isEquivKn→ΩKn+1 : (n : ℕ) → isEquiv (Kn→ΩKn+1 n)
-- -- isEquivKn→ΩKn+1 zero = compEquiv (looper , isEquivLooper) ((cong ∣_∣) , isEquivHelper hLev3) .snd
-- --   where
-- --   hLev3 : (x y : S₊ 1) (p q : x ≡ y) → isProp (p ≡ q)
-- --   hLev3 x y = J (λ y p → (q : x ≡ y) → isProp (p ≡ q) )
-- --                   (transport (λ i → isSet ({!!} (~ i))) isSetInt refl)

-- --     where
-- --     helper : (x ≡ x) ≡ Int
-- --     helper = (λ i → transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x ≡ transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x) ∙
-- --              (λ i → transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x) ≡ transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x)) ∙
-- --               basedΩS¹≡Int (transport (sym S¹≡SuspBool) (transport (sym (ua S1≃SuspBool)) x))
-- -- isEquivKn→ΩKn+1 (suc zero) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn zero (~ i)))
-- --                                         (compEquiv ((trMap (ϕ north)) , isEquiv∣ϕ∣)
-- --                                                    (isoToEquiv {!decodeIso ? ?!})
-- --                                                    .snd) 
-- -- isEquivKn→ΩKn+1 (suc (suc n)) = {!!}


-- -- -- isEquivKn→ΩKn+1 : (n : ℕ) → isEquiv (Kn→ΩKn+1 n)
-- -- -- isEquivKn→ΩKn+1 zero = compEquiv (looper , isEquivLooper) (cong ∣_∣ , isEquivHelper hLevl3) .snd
-- -- --   where
-- -- --   hLevl3 : (x y : S₊ 1) (p q : x ≡ y) → isProp (p ≡ q)
-- -- --   hLevl3 x y = J (λ y p → (q : x ≡ y) → isProp (p ≡ q) )
-- -- --                  (transport (λ i → isSet (helper (~ i))) isSetInt refl)
-- -- --     where
-- -- --     helper : (x ≡ x) ≡ Int
-- -- --     helper = (λ i → transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x ≡ transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x) ∙
-- -- --            (λ i → transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x) ≡ transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x)) ∙
-- -- --            basedΩS¹≡Int (transport (sym S¹≡SuspBool) (transport (sym (ua S1≃SuspBool)) x))
-- -- -- isEquivKn→ΩKn+1 (suc zero) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn zero (~ i)))
-- -- --                                         (compEquiv (trElim (λ _ → isOfHLevelTrunc (2 + (suc zero))) (λ a → ∣ ϕ north a ∣) ,
-- -- --                                                      isEquiv∣ϕ∣)
-- -- --                                                    (truncEquivΩ (ℕ→ℕ₋₂ (suc zero))) .snd)
-- -- -- isEquivKn→ΩKn+1 (suc (suc n)) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn (suc n) (~ i)))
-- -- --                                       (compEquiv (connectedTruncEquiv2 (4 + n) _ (ϕ north) (n , λ i → suc (suc (suc (+-suc n n (~ i))))) ?)
-- -- --                                                  (truncEquivΩ (ℕ→ℕ₋₂ (suc (suc n)))) .snd)

-- -- -- Kn≃ΩKn+1 : (n : ℕ) → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
-- -- -- Kn≃ΩKn+1 n = Kn→ΩKn+1 n , isEquivKn→ΩKn+1 n

-- -- -- ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
-- -- -- ΩKn+1→Kn n a = equiv-proof (isEquivKn→ΩKn+1 n) a .fst .fst
