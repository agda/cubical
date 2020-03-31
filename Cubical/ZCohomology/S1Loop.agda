{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.S1Loop where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification 
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.HITs.Hopf

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


pred₋₂ : ℕ₋₂ → ℕ₋₂
pred₋₂ neg2 = neg2
pred₋₂ neg1 = neg2
pred₋₂ (ℕ→ℕ₋₂ zero) = neg1
pred₋₂ (ℕ→ℕ₋₂ (suc n)) = ℕ→ℕ₋₂ n

is-_-Connected : (n : ℕ₋₂) (f : A → B) → Type _
is-_-Connected {B = B} n f = (x : B) → isContr (∥ fiber f x ∥ n)


Pr2310 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : ℕ₋₂)
         (f : C → A) (g : C → B)  →
         is- n -Connected f →
         is-_-Connected {A = B} {B = Pushout f g} n inr
Pr2310 {A = A} {B = B} {C = C} n f g iscon = {!!}
        where
        module hej {ℓ : Level} (P : (Pushout f g) → HLevel ℓ (2+ n))
                   (h : (b : B) → typ (P (inr b)))
          where
          Q : A → Type _
          Q a = typ (P (inl a))

          fun : (c : C) → Q (f c)
          fun = transport (λ i → (c : C) → typ (P (push c (~ i)))) λ c → h (g c)

          typeFam : (d : Pushout f g) → typ (P d)
          typeFam (inl x) = {!!}
          typeFam (inr x) = {!!}
          typeFam (push a i) = {!!}



Pr242 : (n : ℕ₋₂) → isContr (∥ {!S₊ n!} ∥ pred₋₂ n)
Pr242 = {!!}





-- congFunct : {a b c : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) → cong f (p ∙ q) ≡ cong f p ∙ cong f q
-- congFunct f p q i = hcomp (λ j → λ{(i = i0) → rUnit (cong f (p ∙ q)) (~ j) ;
--                                     (i = i1) → cong f (rUnit p (~ j)) ∙ cong f q})
--                           (cong f (p ∙ (λ k → q (k ∧ (~ i)))) ∙ cong f λ k → q ((~ i) ∨ k) )
--                           -- 
-- symDistr : {a b c : A} (p : a ≡ b) (q : b ≡ c)  → sym (p ∙ q) ≡ sym q ∙ sym p
-- symDistr p q i = hcomp (λ j → λ{(i = i0) → rUnit (sym (p ∙ q)) (~ j)  ;
--                                  (i = i1) → sym (lUnit q (~ j)) ∙ sym p})
--                        (sym ((λ k → p (k ∨ i)) ∙ q) ∙ sym λ k → p (i ∧ k))

-- {- We want to prove that Kn≃ΩKn+1. For this we need the map ϕ-}

-- private
--   ϕ : (pt a : A) → typ (Ω (Susp A , north))
--   ϕ pt a = (merid a) ∙ sym (merid pt)

-- {- To define the map for n=0 we use the λ k → loopᵏ map for S₊ 1. The loop is given by ϕ south north -}


-- looper : Int → _≡_ {A = S₊ 1} north north
-- looper (pos zero) = refl
-- looper (pos (suc n)) = looper (pos n) ∙ (ϕ south north)
-- looper (negsuc zero) = sym (ϕ south north)
-- looper (negsuc (suc n)) = looper (negsuc n) ∙ sym (ϕ south north)

-- {- The map of Kn≃ΩKn+1 is given as follows. -}
-- Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
-- Kn→ΩKn+1 zero x = cong ∣_∣ (looper x)
-- Kn→ΩKn+1 (suc n) = trElim (λ x → (isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc (suc n))) ∣ north ∣ ∣ north ∣))
--                            λ a → cong ∣_∣ ((merid a) ∙ (sym (merid north)))

-- {-
-- We want to show that the function (looper : Int → S₊ 1) defined by λ k → loopᵏ is an equivalece. We already know that the corresponding function (intLoop : Int → S¹ is) an equivalence,
-- so the idea is to show that when intLoop is transported along a suitable path S₊ 1 ≡ S¹ we get looper. Instead of using S₊ 1 straight away, we begin by showing this for the equivalent Susp Bool.
-- -}

-- -- loop for Susp Bool --
-- loop* : _≡_ {A = Susp Bool} north north
-- loop* = merid false ∙ sym (merid true)

-- -- the loop function --
-- intLoop* : Int → _≡_ {A = Susp Bool} north north
-- intLoop* (pos zero) = refl
-- intLoop* (pos (suc n)) = intLoop* (pos n) ∙ loop*
-- intLoop* (negsuc zero) = sym loop*
-- intLoop* (negsuc (suc n)) = intLoop* (negsuc n) ∙ sym loop*

-- -- we show that the loop spaces agree --
-- loopSpId : ΩS¹ ≡ _≡_ {A = Susp Bool} north north
-- loopSpId i = typ (Ω (S¹≡SuspBool i , transp ((λ j → S¹≡SuspBool (j ∧ i))) (~ i) base))

-- -- the transport map --
-- altMap2 : Int → _≡_ {A = Susp Bool} north north
-- altMap2 n i = transport S¹≡SuspBool (intLoop n i)

-- -- We show that the transporting intLoop over S¹≡SuspBool gives intLoop* (modulo function extensionality) --
-- altMap≡intLoop*2 : (x : Int) → intLoop* x ≡ altMap2 x
-- altMap≡intLoop*2 (pos zero) = refl
-- altMap≡intLoop*2 (pos (suc n)) = (λ i → (altMap≡intLoop*2 (pos n) i) ∙ loop*) ∙
--                                  sym (helper n)

--   where
--   helper : (n : ℕ) → altMap2 (pos (suc n)) ≡ altMap2 (pos n) ∙ loop*
--   helper zero = (λ i j → transport S¹≡SuspBool (lUnit loop (~ i) j)) ∙
--                 (λ i j → transport S¹≡SuspBool (loop j)) ∙
--                 (λ i j → transportRefl ((merid false ∙ (sym (merid true))) j) i ) ∙
--                 lUnit loop*
--   helper (suc n) = anotherHelper n ∙
--                    (λ i → altMap2 (pos (suc n)) ∙ helper zero i) ∙
--                    (λ i → altMap2 (pos (suc n)) ∙ lUnit loop* (~ i))
--     where
--     anotherHelper : (n : ℕ) → altMap2 (pos (suc (suc n))) ≡ altMap2 (pos (suc n)) ∙ altMap2 (pos 1)
--     anotherHelper n = ((λ i j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ loop) j))) ∙
--                          rUnit (λ j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ loop) j) ) ∙
--                          (λ i → (λ j → transport S¹≡SuspBool ((intLoop (pos (suc n)) ∙ λ k → loop (k ∧ (~ i))) j)) ∙ λ j → transport S¹≡SuspBool (loop (j ∨ (~ i))) ) ∙
--                          (λ i → (λ j → transport S¹≡SuspBool (rUnit (intLoop (pos (suc n))) (~ i) j)) ∙ λ j → transport S¹≡SuspBool ((lUnit loop i) j))

-- altMap≡intLoop*2 (negsuc zero) = sym ((λ i j → transport S¹≡SuspBool (loop (~ j))) ∙
--                                      λ  i j → transportRefl (loop* (~ j)) i )
-- altMap≡intLoop*2 (negsuc (suc n)) = helper n
--   where
--   altMapneg1 : altMap2 (negsuc zero) ≡ sym (loop*)
--   altMapneg1 i j = transportRefl (loop* (~ j)) i

--   anotherHelper : (n : ℕ) → altMap2 (negsuc (suc n)) ≡ altMap2 (negsuc n) ∙ altMap2 (negsuc zero)
--   anotherHelper n = ((λ i → rUnit (λ j → (transport S¹≡SuspBool ((intLoop (negsuc n) ∙ sym loop) j))) i)) ∙
--                        ((λ i → (λ j → transport S¹≡SuspBool ((intLoop (negsuc n) ∙ (λ k → loop ((~ k) ∨ i))) j)) ∙ λ j → transport S¹≡SuspBool (loop ((~ j) ∧ i)))) ∙
--                        (λ i → ((λ j → transport S¹≡SuspBool (rUnit (intLoop (negsuc n)) (~ i) j))) ∙ altMap2 (negsuc zero))
  
--   helper : (n : ℕ) → intLoop* (negsuc n) ∙ (sym loop*) ≡ altMap2 (negsuc (suc n))
--   helper zero = (λ i → altMapneg1 (~ i) ∙ altMapneg1 (~ i)) ∙ sym (anotherHelper zero)
--   helper (suc n) = (λ i → (helper n i) ∙ altMapneg1 (~ i) ) ∙
--                    sym (anotherHelper (suc n))


-- {- We have that the transported map is an equivalence -}
-- mapIsEquiv : isEquiv altMap2
-- mapIsEquiv = compEquiv (intLoop , (isoToIsEquiv (iso intLoop winding (decodeEncode base) windingIntLoop))) ((λ x i → transport S¹≡SuspBool (x i)) , helper) .snd
--   where
--   helper : isEquiv {A = ΩS¹} {B = _≡_ {A = Susp Bool} north north} (λ x i → transport S¹≡SuspBool (x i))
--   helper = congEquiv (transport S¹≡SuspBool , helper3) .snd
--     where
--     helper2 : transport S¹≡SuspBool ≡ S¹→SuspBool
--     helper2 = funExt λ z → transportRefl (S¹→SuspBool z)
--     helper3 : isEquiv (transport S¹≡SuspBool )
--     helper3 = transport (λ i → isEquiv (helper2 (~ i))) (S¹≃SuspBool .snd)

-- {- From this we get that intLoop* is an equivalence-}
-- intLoop*Equiv : isEquiv intLoop*
-- intLoop*Equiv = transport (λ i → isEquiv (funExt (altMap≡intLoop*2) (~ i))) mapIsEquiv

-- {- We now only need to work with Susp Bool and S₊ 1. We transport intLoop* along a path S1≡SuspBool and show that this gives us looper. -}
-- SuspBool→S1 : Susp Bool → S₊ 1
-- SuspBool→S1 north = north
-- SuspBool→S1 south = south
-- SuspBool→S1 (merid false i) = merid north i
-- SuspBool→S1 (merid true i) = merid south i

-- {- We need to spell out the trivial equivalence S1≃SuspBool. Of course it's important to make sure that we choose the right version of it. -}
-- S1≃SuspBool : Susp Bool ≃ S₊ 1
-- S1≃SuspBool = isoToEquiv (iso SuspBool→S1 S1→SuspBool  retrHelper sectHelper)
--   where
--   S1→SuspBool : S₊ 1 → Susp Bool
--   S1→SuspBool north = north
--   S1→SuspBool south = south
--   S1→SuspBool (merid north i) = merid false i
--   S1→SuspBool (merid south i) = merid true i

--   sectHelper : section S1→SuspBool SuspBool→S1
--   sectHelper north = refl
--   sectHelper south = refl
--   sectHelper (merid false i) = refl
--   sectHelper (merid true i) = refl

--   retrHelper : retract S1→SuspBool SuspBool→S1
--   retrHelper north = refl
--   retrHelper south = refl
--   retrHelper (merid north i) = refl
--   retrHelper (merid south i) = refl

-- {- We show that transporting intLoop* along (ua S1≃SuspBool) gives us looper (again, modulo function extensionality) -}
-- looperIntoBool : (x : Int) → looper x ≡ λ i → transport ((ua (S1≃SuspBool))) (intLoop* x i)
-- looperIntoBool (pos zero) = refl
-- looperIntoBool (pos (suc n)) = (λ j → looperIntoBool (pos n) j ∙ merid north ∙ sym (merid south)) ∙
--                                (λ j → (λ i → transportRefl (SuspBool→S1 (intLoop* (pos n) i)) j ) ∙ merid north ∙ sym (merid south)) ∙
--                                (λ j → cong SuspBool→S1 (intLoop* (pos n)) ∙ congFunct SuspBool→S1 (merid false) (sym (merid true)) (~ j)) ∙
--                                sym (congFunct SuspBool→S1 (intLoop* (pos n)) loop*) ∙
--                                λ j i → transportRefl (SuspBool→S1 ((intLoop* (pos n) ∙ loop*) i)) (~ j)  
-- looperIntoBool (negsuc zero) = symDistr (merid north) (sym (merid south))  ∙
--                                sym (congFunct SuspBool→S1 (merid true) (sym (merid false))) ∙ 
--                                (λ j → cong SuspBool→S1 (merid true ∙ sym (merid false))) ∙
--                                (λ j → cong SuspBool→S1 (symDistr (merid false) (sym (merid true)) (~ j))) ∙
--                                λ j i → transportRefl (SuspBool→S1 (loop* (~ i))) (~ j)
-- looperIntoBool (negsuc (suc n)) = (λ i → looperIntoBool (negsuc n) i ∙ sym ((merid north) ∙ (sym (merid south))) ) ∙
--                                   (λ i → looperIntoBool (negsuc n) i1 ∙ symDistr (merid north) (sym (merid south)) i) ∙
--                                   (λ j → (λ i → transportRefl (SuspBool→S1 (intLoop* (negsuc n) i)) j) ∙ merid south ∙ sym (merid north)) ∙
--                                   (λ j → cong SuspBool→S1 (intLoop* (negsuc n)) ∙ congFunct SuspBool→S1 (merid true) (sym (merid false)) (~ j)) ∙
--                                   ((λ j → cong SuspBool→S1 (intLoop* (negsuc n)) ∙ cong SuspBool→S1 (symDistr (merid false) (sym (merid true)) (~ j)))) ∙
--                                   sym (congFunct SuspBool→S1 (intLoop* (negsuc n)) (sym loop*)) ∙
--                                   λ j i → transportRefl (SuspBool→S1 ((intLoop* (negsuc n) ∙ sym loop*) i)) (~ j)

-- {- From this, we can finally deduce that looper is an equivalence-}
-- isEquivLooper : isEquiv looper
-- isEquivLooper = transport (λ i → isEquiv (funExt (looperIntoBool) (~ i))) isEquivTranspIntLoop
--   where
--   isEquivTranspIntLoop : isEquiv λ x → cong (transport ((ua (S1≃SuspBool)))) (intLoop* x)
--   isEquivTranspIntLoop = compEquiv (intLoop* , intLoop*Equiv)
--                                    (cong (transport (ua S1≃SuspBool)) ,
--                                      congEquiv (transport (ua S1≃SuspBool) ,
--                                                transportEquiv (ua S1≃SuspBool) .snd) .snd) .snd

-- isSetS1 : isSet (_≡_ {A = S₊ 1} north north)
-- isSetS1 = transport (λ i → isSet (helper i)) isSetInt 
--   where
--   helper : Int ≡ (_≡_ {A = S₊ 1} north north)
--   helper = sym ΩS¹≡Int ∙
--            (λ i → typ (Ω (S¹≡SuspBool i , transport (λ j → S¹≡SuspBool (j ∧ i)) base))) ∙
--            (λ i → typ (Ω (ua S1≃SuspBool i , transport (λ j → ua S1≃SuspBool (i ∧ j)) north))) 

-- isEquivHelper2 : isOfHLevel 3 A → isEquiv {B = ∥ A ∥ 1} ∣_∣
-- isEquivHelper2  ofHlevl =
--                isoToIsEquiv (iso ∣_∣
--                                  (trElim (λ _ → ofHlevl) (λ a → a))
--                                  (trElim {B = λ b → ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ ≡ b} (λ b → isOfHLevelSuc 3 (isOfHLevel∥∥ 1) ∣ trElim (λ _ → ofHlevl) (λ a₁ → a₁) b ∣ b) λ a → refl)
--                                  λ b → refl)

-- isEquivHelper : {a b : A} → isOfHLevel 3 A → isEquiv {B = _≡_ {A = ∥ A ∥ 1} ∣ a ∣ ∣ b ∣ } (cong ∣_∣)
-- isEquivHelper {A = A} {a = a} {b = b} ofHlevl = congEquiv (∣_∣ , isEquivHelper2 ofHlevl) .snd


-- S1≡S¹ : S₊ 1 ≡ S¹
-- S1≡S¹ = {!!}


-- d-map : typ (Ω ((Susp S¹) , north)) → S¹ 
-- d-map p = subst HopfSuspS¹ p base

-- d-mapId : (r : S¹) → d-map (ϕ base r) ≡ r
-- d-mapId r = (λ i → subst HopfSuspS¹ (□≡∙ (merid r) (sym (merid base)) (~ i)) base) ∙
--             (substComposite-□ HopfSuspS¹ (merid r) (sym (merid base)) base) ∙
--             test r
--   where
--   test : (r : S¹) → rot r base ≡ r
--   test base = refl
--   test (loop i) = refl


-- testProp : (B : A → Type ℓ') → {!x !}
-- testProp = {!!}


-- S³≡SuspSuspS¹ : S³ ≡ Susp (Susp S¹)
-- S³≡SuspSuspS¹ = S³≡SuspS² ∙ λ i → Susp (S²≡SuspS¹ i)

-- d-mapComp : fiber d-map base ≡ (_≡_ {A = Susp (Susp S¹)} north north)
-- d-mapComp = sym (pathSigma≡sigmaPath {B = HopfSuspS¹} _ _) ∙ helper 
--   where
--   helper : (_≡_ {A = Σ (Susp S¹) λ x → HopfSuspS¹ x} (north , base) (north , base)) ≡ (_≡_ {A = Susp (Susp S¹)} north north)
--   helper = (λ i → (_≡_ {A = S³≡TotalHopf (~ i)}
--                         (transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))
--                         ((transp (λ j → S³≡TotalHopf (~ i ∨ ~ j)) (~ i) (north , base))))) ∙
--            (λ i → _≡_ {A = S³} base base) ∙
--            (λ i → _≡_ {A = S³≡SuspSuspS¹ i} (transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base) ((transp (λ j → S³≡SuspSuspS¹ (i ∧ j)) (~ i) base)))

-- n=1Equiv : isEquiv {A = S₊ 1} {B = typ (Ω ((S₊ 2) , north))} (ϕ north)
-- n=1Equiv = isoToIsEquiv (iso (ϕ north)
--                              (λ x → {!(cong (transport (λ i → Susp (sym (S¹≡SuspBool) i))) (cong (transport (λ i → Susp ((sym (ua S1≃SuspBool)) i))) x))!})
--                              {!Hopf!}
--                              {!HopfSuspS¹ !})
--          where
--          helper : transport (λ i → Susp ((S¹≡SuspBool) (~ i))) (transport (λ i → Susp (ua S1≃SuspBool (~ i))) north) ≡ north
--          helper = refl -- fantastic

-- is1Connected-dmap : is- 1 -Connected d-map
-- is1Connected-dmap base = transport (λ j → isContr (∥ d-mapComp (~ j) ∥ ℕ→ℕ₋₂ 1)) {!!}
-- is1Connected-dmap (loop i) = {!!}

-- isOfHLevelLemma : (n : ℕ₋₂) → isOfHLevel (2+ n) A → isOfHLevel (suc (2+ n)) (Susp A)
-- isOfHLevelLemma neg2 hlvl = λ x y → {!!}
-- isOfHLevelLemma neg1 hlvl = {!!}
-- isOfHLevelLemma (ℕ→ℕ₋₂ n) hlvl = {!!}
--   where
--   helper : (n : ℕ) → isOfHLevel n A → (x y : Susp A) → isOfHLevel (suc n) (x ≡ y)
--   helper zero hlvl north north = {!s!}
--   helper zero hlvl north south = {!!}
--   helper zero hlvl north (merid a i) = {!!}
--   helper zero hlvl south north = {!!}
--   helper zero hlvl south south = {!!}
--   helper zero hlvl south (merid a i) = {!!}
--   helper zero hlvl (merid a i) y = {!!}
--   helper (suc n) hlvl x y = {!!}

-- -- Kn→ΩKn+1Sucn : (n : ℕ) → Kn→ΩKn+1 (suc n) ≡ λ x → truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc n))) (λ a → ∣ ϕ north a ∣) x) -- 
-- -- Kn→ΩKn+1Sucn n = funExt (trElim (λ x → isOfHLevelSuc (suc (suc n))
-- --                                                        ((isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc (suc n))) ∣ north ∣ ∣ north ∣)
-- --                                                                      (Kn→ΩKn+1 (suc n) x)
-- --                                                                      (truncEquivΩ (ℕ→ℕ₋₂ (suc n)) .fst (trElim (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc n))) (λ a → ∣ ϕ north a ∣) x))))
-- --                                  λ a → refl)


-- -- isEquivKn→ΩKn+1 : (n : ℕ) → isEquiv (Kn→ΩKn+1 n)
-- -- isEquivKn→ΩKn+1 zero = compEquiv (looper , isEquivLooper) (cong ∣_∣ , isEquivHelper hLevl3) .snd
-- --   where
-- --   hLevl3 : (x y : S₊ 1) (p q : x ≡ y) → isProp (p ≡ q)
-- --   hLevl3 x y = J (λ y p → (q : x ≡ y) → isProp (p ≡ q) )
-- --                  (transport (λ i → isSet (helper (~ i))) isSetInt refl)
-- --     where
-- --     helper : (x ≡ x) ≡ Int
-- --     helper = (λ i → transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x ≡ transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x) ∙
-- --            (λ i → transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x) ≡ transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x)) ∙
-- --            basedΩS¹≡Int (transport (sym S¹≡SuspBool) (transport (sym (ua S1≃SuspBool)) x))
-- -- isEquivKn→ΩKn+1 (suc zero) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn zero (~ i)))
-- --                                         (compEquiv (trElim (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc zero))) (λ a → ∣ ϕ north a ∣) ,
-- --                                                      {!!})
-- --                                                    (truncEquivΩ (ℕ→ℕ₋₂ (suc zero))) .snd)
-- -- isEquivKn→ΩKn+1 (suc (suc n)) = {!!}
