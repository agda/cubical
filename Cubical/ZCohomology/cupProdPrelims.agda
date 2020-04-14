{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.cupProdPrelims where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to +Int)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.HITs.Hopf
open import Cubical.HITs.Truncation.Connected.Base public
open import Cubical.HITs.Truncation.Connected.Properties public

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

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

----------------------------------- n = 1 -----------------------------------------------------

{- We begin by stating some useful lemmas -}

sphereConnectedSpecCase : is- 2 -ConnectedType (Susp (Susp S¹))
sphereConnectedSpecCase = transport (λ i → is- 2 -ConnectedType (helper i)) (sphereConnected 3)
  where
  helper : S₊ 3 ≡ Susp (Susp S¹)
  helper = (λ i → Susp (Susp (Susp (ua Bool≃Susp⊥ (~ i))))) ∙ λ i → Susp (Susp (S¹≡SuspBool (~ i)))

S¹≡S1 : S₊ 1 ≡ S¹
S¹≡S1 = (λ i → Susp (ua (Bool≃Susp⊥) (~ i))) ∙ sym S¹≡SuspBool

S³≡SuspSuspS¹ : S³ ≡ Susp (Susp S¹)
S³≡SuspSuspS¹ = S³≡SuspS² ∙ λ i → Susp (S²≡SuspS¹ i)

isSetS1 : isSet (Path (S₊ 1) north north)
isSetS1 = transport (λ i → isSet (helper i)) isSetInt 
  where
  helper : Int ≡ (Path (S₊ 1) north north)
  helper = sym ΩS¹≡Int ∙
           (λ i → typ (Ω (S¹≡SuspBool i , transport (λ j → S¹≡SuspBool (j ∧ i)) base))) ∙
           (λ i → typ (Ω (ua S1≃SuspBool i , transport (λ j → ua S1≃SuspBool (i ∧ j)) north))) 

isEquivHelper2 : isOfHLevel 3 A → isEquiv {B = ∥ A ∥ 1} ∣_∣
isEquivHelper2  ofHlevl =
               isoToIsEquiv (iso ∣_∣
                                 (trElim (λ _ → ofHlevl) (λ a → a))
                                 (trElim {B = λ b → ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ ≡ b}
                                         (λ b → isOfHLevelSuc 3 (isOfHLevelTrunc 3)
                                                                 ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ b)
                                         λ a → refl)
                                 λ b → refl)

isEquivHelper : {a b : A} → isOfHLevel 3 A → isEquiv {B = Path (∥ A ∥ 1) ∣ a ∣ ∣ b ∣ } (cong ∣_∣)
isEquivHelper {A = A} {a = a} {b = b} ofHlevl = congEquiv (∣_∣ , isEquivHelper2 ofHlevl) .snd

{- We give the following map and show that it is an equivalence -}

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
d-mapComp = sym (pathSigma≡sigmaPath {B = HopfSuspS¹} _ _) ∙ helper 
  where
  helper : Path (Σ (Susp S¹) λ x → HopfSuspS¹ x) (north , base) (north , base) ≡ Path (Susp (Susp S¹)) north north
  helper = (λ i → (_≡_ {A = S³≡TotalHopf (~ i)}
                        (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
                        ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))))) ∙
           (λ i → _≡_ {A = S³} base base) ∙
           (λ i → _≡_ {A = S³≡SuspSuspS¹ i} (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))


is1Connected-dmap : is- 1 -Connected d-map
is1Connected-dmap base = transport (λ j → isContr (∥ d-mapComp (~ j) ∥ ℕ→ℕ₋₂ 1))
                                   (transport (λ i →  isContr (PathΩ {A = Susp (Susp S¹)} {a = north} (ℕ→ℕ₋₂ 1) i))
                                              (refl , isOfHLevelSuc 1 (isOfHLevelSuc 0 sphereConnectedSpecCase) ∣ north ∣ ∣ north ∣ (λ _ → ∣ north ∣)))
is1Connected-dmap (loop j) = 
               hcomp (λ k → λ{(j = i0) → is1Connected-dmap base ;
                               (j = i1) → isPropIsOfHLevel 0 (transport (λ i → isContr (∥ fiber d-map (loop i) ∥ ℕ→ℕ₋₂ 1))
                                                                         (is1Connected-dmap base))
                                                              (is1Connected-dmap base)
                                                              k})
                     (transp (λ i → isContr (∥ fiber d-map (loop (i ∧ j)) ∥ ℕ→ℕ₋₂ 1)) (~ j)
                             (transport (λ j → isContr (∥ d-mapComp (~ j) ∥ ℕ→ℕ₋₂ 1))
                                   (transport (λ i →  isContr (PathΩ {A = Susp (Susp S¹)} {a = north} (ℕ→ℕ₋₂ 1) i))
                                              (refl , isOfHLevelSuc 1 (isOfHLevelSuc 0 sphereConnectedSpecCase) ∣ north ∣ ∣ north ∣ (λ _ → ∣ north ∣)))))

d-equiv : isEquiv {A = ∥  typ (Ω (Susp S¹ , north)) ∥ (ℕ→ℕ₋₂ 1)} {B = ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (trElim (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣ )
d-equiv = conEquiv (ℕ→ℕ₋₂ 1) d-map is1Connected-dmap .snd

{- We show that composing (λ a → ∣ ϕ base a ∣) and (λ x → ∣ d-map x ∣) gives us the identity function.  -}

d-mapId2 : (λ (x : ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)) → (trElim {n = 3} {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
                                             (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣) x)) ≡ λ x → x
d-mapId2 = funExt (trElim (λ x → isOfHLevelSuc 2 (isOfHLevelTrunc 3 ((trElim {n = 3}
                                                                              {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)}
                                                                              (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
                                                                              (trElim (λ _ → isOfHLevelTrunc 3)
                                                                                      (λ a → ∣ ϕ base a ∣) x)) x))
                          λ a i → ∣ d-mapId a i ∣)

{- This means that (λ a → ∣ ϕ base a ∣) is an equivalence -}
isEquiv∣ϕ-base∣ : isEquiv {A = ∥ S¹ ∥ ℕ→ℕ₋₂ 1} (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣))
isEquiv∣ϕ-base∣ = composesToId→Equiv (trElim {n = 3} {B = λ _ → ∥ S¹ ∥ (ℕ→ℕ₋₂ 1)} (λ x → isOfHLevelTrunc 3) λ x → ∣ d-map x ∣)
                          (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ base a ∣))
                          d-mapId2
                          d-equiv

---------------------------------
-- We cheat when n = 1 and use J to prove the following lemmma.  There is an obvious dependent path between ϕ base and ϕ north. Since the first one is an equivalence, so is the other.
-- 
pointFunEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ} {C : (A : Type ℓ) (a1 : A) → Type ℓ'} (p : A ≡ B) (a : A) (b : B) →
            (transport p a ≡ b) →
            (f : (A : Type ℓ) →
            (a1 : A) (a2 : ∥ A ∥ 1)  → C A a1) →
            isEquiv (f A a) →
            isEquiv (f B b)
pointFunEquiv {ℓ = ℓ}{A = A} {B = B} {C = C} =
         J (λ B p → (a : A) (b : B) →
                      (transport p a ≡ b) →
                      (f : (A : Type ℓ) →
                      (a1 : A) (a2 : ∥ A ∥ 1)  → C A a1) →
                      isEquiv (f A a) →
                      isEquiv (f B b))
           λ a b trefl f is → transport (λ i → isEquiv (f A ((sym (transportRefl a) ∙ trefl) i))) is

{- By pointFunEquiv, this gives that λ a → ∣ ϕ north a ∣ is an equivalence. -}

isEquiv∣ϕ∣ : isEquiv {A = ∥ S₊ 1 ∥ 1} {B = ∥ typ (Ω (S₊ 2 , north)) ∥ 1} (trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ north a ∣))
isEquiv∣ϕ∣ = pointFunEquiv {A = S¹} (λ i → S¹≡S1 (~ i)) base north refl (λ A a1 → trElim (λ _ → isOfHLevelTrunc 3) (λ a → ∣ ϕ a1 a ∣)) isEquiv∣ϕ-base∣

---------------------------------------------------- Finishing up ---------------------------------

{- For n ≥ 1, we rewrite our function as the composition below. -}
Kn→ΩKn+1Sucn : (n : ℕ) → Kn→ΩKn+1 (suc n) ≡ λ x → truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (3 + n)) (λ a → ∣ ϕ north a ∣) x)
Kn→ΩKn+1Sucn n = funExt (trElim (λ x → isOfHLevelSuc (suc (suc n))
                                                       ((isOfHLevelTrunc ( 2 + (suc (suc n))) ∣ north ∣ ∣ north ∣)
                                                                     (Kn→ΩKn+1 (suc n) x)
                                                                     (truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevelTrunc (2 + (suc n))) (λ a → ∣ ϕ north a ∣) x))))
                                 λ a → refl)



