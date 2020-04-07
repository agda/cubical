{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.Properties where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-14
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-1
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-2
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-4
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties renaming (elim to trElim)
open import Cubical.HITs.Nullification

open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

isConnectedSubtr : (n m : ℕ) (f : A → B) → is- (-2+ (n + m)) -Connected f → is- (-2+ n) -Connected f
isConnectedSubtr n m f iscon b = transport (λ i → isContr (ua (truncOfTruncEq {A = fiber f b} n m) (~ i) ))
                                           (∣ iscon b .fst ∣ ,
                                             trElim (λ x → isOfHLevelPath n (isOfHLevel∥∥ (-2+ n)) _ _)
                                                    λ a → cong ∣_∣ (iscon b .snd a))
--

{-
The "induction principle" for n-connected functions from the HoTT book (see Lemma 7.5.7):

For n ≥ -2, f : A → B, P : B → Type, TFAE:
1. f in n-connected
2. For every B → n-Type, the map (indConFun f p) is an equivalence
3. For every B → n-Type, the map (indConFun f p) has a section
-}

module elim (f : A → B) (n : ℕ₋₂) where
  1→2 : ∀ {ℓ} → is- n -Connected f →
              (P : B → HLevel ℓ (2+ n)) →
              isEquiv (indConFun f P)
  1→2 = conInd-i→ii f n

  2→3 : ∀ {ℓ} (P : B → HLevel ℓ (2+ n)) →
              isEquiv (indConFun f P) →
              hasSection (indConFun f P)
  2→3 = conInd-ii→iii f n

  3→1 : (∀ {ℓ} (P : B → HLevel ℓ (2+ n)) →
        hasSection (indConFun f P)) →
        is- n -Connected f
  3→1 = conInd-iii→i f n

{- a function from Unit to an (n + 1)-connected type is n-connected -}
trivFunCon : ∀{ℓ} {A : Type ℓ} {a : A} → (n : ℕ₋₂) → (is- (suc₋₂ n) -ConnectedType A) → is- n -Connected (λ (x : Unit) → a)
trivFunCon = Lemma7-5-11

trivFunCon← : ∀{ℓ} {A : Type ℓ} {a : A} → (n : ℕ₋₂) → is- n -Connected (λ (x : Unit) → a) → (is- (suc₋₂ n) -ConnectedType A)
trivFunCon← = Lemma7-5-11←

{- n-connected functions induce equivalences between n-truncations -}
conEquiv : (n : ℕ₋₂) (f : A → B) → (is- n -Connected f) → ∥ A ∥ n ≃ ∥ B ∥ n
conEquiv = Lemma7-5-14

conEquiv2 : (n m : ℕ) (f : A → B) → (is- (-2+ (n + m)) -Connected f) → ∥ A ∥ (-2+ n) ≃ ∥ B ∥ (-2+ n)
conEquiv2 n m f iscon = conEquiv (-2+ n) f (isConnectedSubtr n m f iscon)

conEquiv3 : (n m : ℕ) (f : A → B) → Σ[ x ∈ ℕ ] n + x ≡ m →  (is- (-2+ m) -Connected f) → ∥ A ∥ (-2+ n) ≃ ∥ B ∥ (-2+ n)
conEquiv3 n m f (x , pf) iscon  = conEquiv (-2+ n) f (isConnectedSubtr n x f (transport (λ i → is- (-2+ pf (~ i)) -Connected f) iscon)) -- 

{- Wedge connectivity lemma (Lemma 8.6.2 in the HoTT book) -}
WedgeConn : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ) →
            (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) →
            (is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B)) →
            (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m)))) →
            (f : ((a : (typ A)) → fst (P a (pt B)))) →
            (g : ((b : (typ B)) → fst (P (pt A) b))) →
            (p : f (pt A) ≡ g (pt B)) →
            Σ ((a : typ A) → (b : typ B) → fst (P a b))
              λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b))
                       λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)
WedgeConn = Lemma8-6-2

--------- Freudenthal -------

FthalFun : A → A → typ (Ω ((Susp A) , north))
FthalFun a x = merid x ∙ sym (merid a)

abstract
  FthalFun-2nConnected : (n : ℕ) (a : A)
                         (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                         is- ℕ→ℕ₋₂ (n + n) -Connected (FthalFun a)
  FthalFun-2nConnected n a iscon = Thm8-6-4 n a iscon

  Freudenthal : (n : ℕ) (A : Pointed ℓ) →
                is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) →
                ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≃ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
  Freudenthal n A iscon = conEquiv _ (FthalFun (pt A)) (FthalFun-2nConnected n (pt A) iscon)


------------------------------

