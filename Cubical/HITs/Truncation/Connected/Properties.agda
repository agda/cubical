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
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties renaming (elim to trElim)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Sn.Base
open import Cubical.Data.Unit.Properties

open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

isConnectedSubtr : (n m : ℕ) (f : A → B) → is- (-2+ (n + m)) -Connected f → is- (-2+ n) -Connected f
isConnectedSubtr n m f iscon b = transport (λ i → isContr (ua (truncOfTruncEq {A = fiber f b} n m) (~ i) ))
                                           (∣ iscon b .fst ∣ ,
                                             trElim (λ x → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
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


inrConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : ℕ₋₂)
         (f : C → A) (g : C → B)  →
         is- n -Connected f →
         is-_-Connected {A = B} {B = Pushout f g} n inr
inrConnected {A = A} {B = B} {C = C} n f g iscon = elim.3→1 inr n λ P → (λ k → helpLemmas.k P k) , λ b  → refl
        where
        module helpLemmas {ℓ : Level} (P : (Pushout f g) → HLevel ℓ (2+ n))
                   (h : (b : B) → typ (P (inr b)))
          where
          Q : A → HLevel _ (2+ n)
          Q a = (P (inl a))

          fun : (c : C) → typ (Q (f c))
          fun c = transport (λ i → typ (P (push c (~ i)))) (h (g c))

          k : (d : Pushout f g) → typ (P d)
          k (inl x) = elim.2→3 f n Q (elim.1→2 f n iscon Q) .fst fun x  
          k (inr x) = h x
          k (push a i) = hcomp (λ k → λ{(i = i0) → elim.2→3 f n Q
                                                                     (elim.1→2 f n iscon Q) .fst
                                                                     fun (f a) ;
                                               (i = i1) → transportTransport⁻ (λ j → typ (P (push a j))) (h (g a)) k})
                                     (transp (λ j → typ (P (push a (i ∧ j))))
                                             (~ i)
                                             (elim.2→3 f n Q
                                                        (elim.1→2 f n iscon Q) .snd fun i a))


sphereConnected : (n : ℕ) → is- (-1+ n) -ConnectedType (S₊ n)   
sphereConnected zero = ∣ north ∣ , (isOfHLevelTrunc 1 ∣ north ∣)
sphereConnected (suc n) = transport (λ i → is- ℕ→ℕ₋₂ n -ConnectedType (Susp≡Push {A = S₊ n} (~ i)))
                          (trivFunCon← {A = Pushout {A = S₊ n} (λ x → tt) λ x → tt} {a = inr tt } _
                                        (transport (λ i → is- (-1+ n) -Connected (mapsAgree (~ i)))
                                                   (inrConnected _ (λ x → tt) (λ x → tt) λ{tt → transport (λ i → isContr (∥ fibUnit (~ i) ∥ (-1+ n))) (sphereConnected n)})))
  where
  mapsAgree : Path ((x : Unit) → Pushout {A = S₊ n} (λ x → tt) (λ x → tt)) (λ (x : Unit) → inr tt) inr 
  mapsAgree = funExt λ {tt → refl}
  
  fibUnit : fiber (λ (x : S₊ n) → tt) tt ≡ S₊ n
  fibUnit = isoToPath (iso (λ b → fst b) (λ a → a , refl) (λ b → refl) λ b i → (fst b) , isProp→isSet isPropUnit tt tt refl (snd b) i)

  Susp≡Push : Susp A ≡ Pushout {A = A} (λ a → tt) λ a → tt
  Susp≡Push {A = A} = isoToPath (iso fun inverse sect retr)
    where
    fun : Susp A → Pushout {A = A} (λ a → tt) (λ a → tt)
    fun north = inl tt
    fun south = inr tt
    fun (merid a i) = push a i
    inverse : Pushout {A = A} (λ a → tt) (λ a → tt) → Susp A
    inverse (inl tt) = north
    inverse (inr tt) = south
    inverse (push a i) = merid a i

    sect : section fun inverse
    sect (inl tt) = refl
    sect (inr tt) = refl
    sect (push a i) = refl

    retr : retract fun inverse
    retr north = refl
    retr south = refl
    retr (merid a i) = refl
