{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Properties where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
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
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
-- open import Cubical.HITs.SmashProduct.Base
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup

open import Cubical.ZCohomology.KcompPrelims

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ

infixr 34 _+ₖ_
infixr 34 _+ₕ_

open Iso renaming (inv to inv')
rUnitlUnitGen : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {b : B} (e : Iso A (b ≡ b))
                (0A : A)
                (0fun : fun e 0A ≡ refl)
              → Path (inv' e (fun e 0A ∙ fun e 0A) ≡ 0A)
                     (cong (inv' e) (cong (_∙ fun e 0A) 0fun) ∙∙ cong (inv' e) (sym (lUnit (fun e 0A))) ∙∙ Iso.leftInv e 0A)
                     (cong (inv' e) (cong (fun e 0A ∙_) 0fun) ∙∙ cong (inv' e) (sym (rUnit (fun e 0A))) ∙∙ Iso.leftInv e 0A)
rUnitlUnitGen e 0A 0fun =
    (λ i → cong (inv' e) (cong (_∙ fun e 0A) 0fun) ∙∙ rUnit (cong (inv' e) (sym (lUnit (fun e 0A)))) i ∙∙ Iso.leftInv e 0A)
  ∙ ((λ i → (λ j → inv' e (0fun (~ i ∧ j) ∙ 0fun (j ∧ i))) ∙∙ ((λ j → inv' e (0fun (~ i ∨ j) ∙ 0fun i)) ∙∙ cong (inv' e) (sym (lUnit (0fun i))) ∙∙ λ j → inv' e (0fun (i ∧ (~ j)))) ∙∙ Iso.leftInv e 0A)
  ∙∙ (λ i → (λ j → inv' e (fun e 0A ∙ 0fun j)) ∙∙ (λ j → inv' e (0fun (j ∧ ~ i) ∙ refl)) ∙∙ cong (inv' e) (sym (rUnit (0fun (~ i)))) ∙∙ (λ j → inv' e (0fun (~ i ∧ ~ j))) ∙∙ Iso.leftInv e 0A)
  ∙∙ λ i → cong (inv' e) (cong (fun e 0A ∙_) 0fun) ∙∙ rUnit (cong (inv' e) (sym (rUnit (fun e 0A)))) (~ i)  ∙∙ Iso.leftInv e 0A)

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

-----------

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

---------- Algebra/Group stuff --------

0ₖ : (n : ℕ) → coHomK n
0ₖ zero = pt (coHomK-ptd 0)
0ₖ (suc zero) = pt (coHomK-ptd 1)
0ₖ (suc (suc n)) = pt (coHomK-ptd (2 + n))

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = n} x y  = ΩKn+1→Kn n (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)

-ₖ_ : {n : ℕ} →  coHomK n → coHomK n
-ₖ_ {n = n} x = ΩKn+1→Kn n (sym (Kn→ΩKn+1 n x))

-- subtraction as a binary operator
_-ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_-ₖ_  {n = n} x y  = ΩKn+1→Kn n (Kn→ΩKn+1 n x ∙ sym (Kn→ΩKn+1 n y))

+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

-'ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
-'ₖ-syntax n = _-ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x
syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = sym (rUnit refl)
Kn→ΩKn+10ₖ (suc zero) i j = ∣ (rCancel (merid base) i j) ∣
Kn→ΩKn+10ₖ (suc (suc n)) i j = ∣ (rCancel (merid north) i j) ∣

ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
ΩKn+1→Kn-refl zero = refl
ΩKn+1→Kn-refl (suc zero) = refl
ΩKn+1→Kn-refl (suc (suc zero)) = refl
ΩKn+1→Kn-refl (suc (suc (suc zero))) = refl
ΩKn+1→Kn-refl (suc (suc (suc (suc zero)))) = refl
ΩKn+1→Kn-refl (suc (suc (suc (suc (suc n))))) = refl

-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ {n = n} = (λ i → ΩKn+1→Kn n (sym (Kn→ΩKn+10ₖ n i)))
           ∙∙ (λ i → ΩKn+1→Kn n (Kn→ΩKn+10ₖ n (~ i)))
           ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) (0ₖ n)

+ₖ→∙ : (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (a +[ n ]ₖ b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
+ₖ→∙ n a b = Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b)

lUnitₖ : (n : ℕ) (x : coHomK n) → (0ₖ n) +[ n ]ₖ x ≡ x
lUnitₖ 0 x = Iso.leftInv (Iso-Kn-ΩKn+1 zero) x
lUnitₖ (suc zero) = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ x → Iso.leftInv (Iso-Kn-ΩKn+1 1) ∣ x ∣
lUnitₖ (suc (suc n)) x =
  (λ i → ΩKn+1→Kn (2 + n) (Kn→ΩKn+10ₖ (2 + n) i ∙ Kn→ΩKn+1 (2 + n) x)) ∙∙
                       (cong (ΩKn+1→Kn (2 + n)) (sym (lUnit (Kn→ΩKn+1 (2 + n) x)))) ∙∙
                       Iso.leftInv (Iso-Kn-ΩKn+1 (2 + n)) x
rUnitₖ : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ 0 x = Iso.leftInv (Iso-Kn-ΩKn+1 zero) x
rUnitₖ (suc zero) = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ x → Iso.leftInv (Iso-Kn-ΩKn+1 1) ∣ x ∣
rUnitₖ (suc (suc n)) x =
    (λ i → ΩKn+1→Kn (2 + n) (Kn→ΩKn+1 (2 + n) x ∙ Kn→ΩKn+10ₖ (2 + n) i))
  ∙∙ (cong (ΩKn+1→Kn (2 + n)) (sym (rUnit (Kn→ΩKn+1 (2 + n) x))))
  ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 (2 + n)) x

rCancelₖ  : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (-[ n ]ₖ x) ≡ (0ₖ n)
rCancelₖ zero x = (λ i → ΩKn+1→Kn 0 (Kn→ΩKn+1 zero x ∙ Iso.rightInv (Iso-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i)) ∙
                        cong (ΩKn+1→Kn 0) (rCancel (Kn→ΩKn+1 zero x))
rCancelₖ (suc n) x = (λ i → ΩKn+1→Kn (suc n) (Kn→ΩKn+1 (1 + n) x ∙ Iso.rightInv (Iso-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i)) ∙
                               cong (ΩKn+1→Kn (suc n)) (rCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (suc n) (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))

lCancelₖ : (n : ℕ) (x : coHomK n) → (-[ n ]ₖ x) +[ n ]ₖ x  ≡ (0ₖ n)
lCancelₖ 0 x = (λ i → ΩKn+1→Kn 0 (Iso.rightInv (Iso-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i ∙ Kn→ΩKn+1 zero x)) ∙
                        cong (ΩKn+1→Kn 0) (lCancel (Kn→ΩKn+1 zero x))
lCancelₖ (suc n) x = (λ i → ΩKn+1→Kn (suc n) (Iso.rightInv (Iso-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i ∙ Kn→ΩKn+1 (1 + n) x)) ∙
                               cong (ΩKn+1→Kn (suc n)) (lCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → (ΩKn+1→Kn (suc n)) (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))

assocₖ : (n : ℕ) (x y z : coHomK n) → ((x +[ n ]ₖ y) +[ n ]ₖ z) ≡ (x +[ n ]ₖ (y +[ n ]ₖ z))
assocₖ n x y z = ((λ i → ΩKn+1→Kn n (Kn→ΩKn+1 n (ΩKn+1→Kn n (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)) ∙ Kn→ΩKn+1 n z)) ∙∙
                          (λ i → ΩKn+1→Kn n (Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i ∙ Kn→ΩKn+1 n z)) ∙∙
                          (λ i → ΩKn+1→Kn n (assoc (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) (Kn→ΩKn+1 n z) (~ i)))) ∙
                          (λ i → ΩKn+1→Kn n ((Kn→ΩKn+1 n x) ∙ Iso.rightInv (Iso-Kn-ΩKn+1 n) ((Kn→ΩKn+1 n y ∙ Kn→ΩKn+1 n z)) (~ i)))

cancelₖ : (n : ℕ) (x : coHomK n) → x -[ n ]ₖ x ≡ (0ₖ n)
cancelₖ zero x = cong (ΩKn+1→Kn 0) (rCancel (Kn→ΩKn+1 zero x))
cancelₖ (suc zero) x = cong (ΩKn+1→Kn 1) (rCancel (Kn→ΩKn+1 1 x))
cancelₖ (suc (suc zero)) x = cong (ΩKn+1→Kn 2) (rCancel (Kn→ΩKn+1 2 x))
cancelₖ (suc (suc (suc zero))) x = cong (ΩKn+1→Kn 3) (rCancel (Kn→ΩKn+1 3 x))
cancelₖ (suc (suc (suc (suc zero)))) x = cong (ΩKn+1→Kn 4) (rCancel (Kn→ΩKn+1 4 x))
cancelₖ (suc (suc (suc (suc (suc n))))) x = cong (ΩKn+1→Kn (5 + n)) (rCancel (Kn→ΩKn+1 (5 + n) x))

-rUnitₖ : (n : ℕ) (x : coHomK n) → x -[ n ]ₖ 0ₖ n ≡ x
-rUnitₖ zero x = rUnitₖ zero x
-rUnitₖ (suc n) x = cong (λ y → ΩKn+1→Kn (suc n) (Kn→ΩKn+1 (suc n) x ∙ sym y)) (Kn→ΩKn+10ₖ (suc n))
                 ∙∙ cong (ΩKn+1→Kn (suc n)) (sym (rUnit (Kn→ΩKn+1 (suc n) x)))
                 ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) x

isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

-- not proved as a special case of isCommΩKn, in order to avoid congIso
abstract
  isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A → isOfHLevel (suc n) (typ A) → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
  isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
      ((λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
   ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
   ∙∙ (λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

  isCommΩK1 : (n : ℕ) → isComm∙ ((Ω^ n) (coHomK-ptd 1)) -- (p q : typ ((Ω^ (suc n)) (coHomK-ptd 1))) → p ∙ q ≡ q ∙ p
  isCommΩK1 zero = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK1 (suc n) = Eckmann-Hilton n

  open Iso renaming (inv to inv')
  ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , Iso.fun e (pt A))
  ptdIso→comm {A = (A , a)} {B = B} e comm p q =
         sym (rightInv (congIso e) (p ∙ q))
      ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                              ∙∙ (comm (inv' (congIso e) p) (inv' (congIso e) q))
                              ∙∙ (sym (invCongFunct e q p))))
      ∙∙ rightInv (congIso e) (q ∙ p)

  isCommΩK : (n : ℕ) → isComm∙ (coHomK-ptd n)
  isCommΩK zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
  isCommΩK (suc zero) = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK (suc (suc n)) = subst isComm∙ (λ i → coHomK (2 + n) , ΩKn+1→Kn-refl (2 + n) i) (ptdIso→comm {A = (_ , _)} (invIso (Iso-Kn-ΩKn+1 (2 + n))) (Eckmann-Hilton 0))

commₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) ≡ (y +[ n ]ₖ x)
commₖ 0 x y i = ΩKn+1→Kn 0 (isCommΩK1 0 (Kn→ΩKn+1 0 x) (Kn→ΩKn+1 0 y) i)
commₖ 1 x y i = ΩKn+1→Kn 1 (ptdIso→comm {A = ((∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (HubAndSpoke (S₊ 3) 3 , ∣ north ∣)))}
                                        {B = coHomK 2}
                                        (invIso (Iso-Kn-ΩKn+1 2)) (Eckmann-Hilton 0) (Kn→ΩKn+1 1 x) (Kn→ΩKn+1 1 y) i)
commₖ 2 x y i = ΩKn+1→Kn 2 (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (HubAndSpoke (S₊ 4) 4 , ∣ north ∣))}
                                        {B = coHomK 3}
                                        (invIso (Iso-Kn-ΩKn+1 3)) (Eckmann-Hilton 0) (Kn→ΩKn+1 2 x) (Kn→ΩKn+1 2 y) i)
commₖ 3 x y i = ΩKn+1→Kn 3 (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (HubAndSpoke (S₊ 5) 5 , ∣ north ∣))}
                                        {B = coHomK 4}
                                        (invIso (Iso-Kn-ΩKn+1 4)) (Eckmann-Hilton 0) (Kn→ΩKn+1 3 x) (Kn→ΩKn+1 3 y) i)
commₖ (suc (suc (suc (suc n)))) x y i =
  ΩKn+1→Kn (4 + n) (ptdIso→comm {A = (∣ north ∣ ≡ ∣ north ∣) , snd ((Ω^ 1) (HubAndSpoke (S₊ (6 + n)) (ℕ→ℕ₋₁ (6 + n)) , ∣ north ∣))}
                                {B = coHomK (5 + n)}
                                (invIso (Iso-Kn-ΩKn+1 (5 + n))) (Eckmann-Hilton 0) (Kn→ΩKn+1 (4 + n) x) (Kn→ΩKn+1 (4 + n) y) i)


rUnitₖ' : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ' n x = commₖ n x (0ₖ n) ∙ lUnitₖ n x

-distrₖ : (n : ℕ) (x y : coHomK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ n x y = ((λ i → ΩKn+1→Kn n (sym (Kn→ΩKn+1 n (ΩKn+1→Kn n (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y))))) ∙∙
                      (λ i → ΩKn+1→Kn n (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i))) ∙∙
                      (λ i → ΩKn+1→Kn n (symDistr (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i))) ∙∙
                      (λ i → ΩKn+1→Kn n (Iso.rightInv (Iso-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n y)) (~ i) ∙ (Iso.rightInv (Iso-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n x)) (~ i)))) ∙∙
                      commₖ n (-[ n ]ₖ y) (-[ n ]ₖ x)

private
  rCancelLem : (n : ℕ) (x : coHomK n) → ΩKn+1→Kn n ((Kn→ΩKn+1 n x) ∙ refl) ≡ ΩKn+1→Kn n (Kn→ΩKn+1 n x)
  rCancelLem zero x = refl
  rCancelLem (suc n) x = cong (ΩKn+1→Kn (suc n)) (sym (rUnit (Kn→ΩKn+1 (suc n) x)))

  lCancelLem : (n : ℕ) (x : coHomK n) → ΩKn+1→Kn n (refl ∙ (Kn→ΩKn+1 n x)) ≡ ΩKn+1→Kn n (Kn→ΩKn+1 n x)
  lCancelLem zero x = refl
  lCancelLem (suc n) x = cong (ΩKn+1→Kn (suc n)) (sym (lUnit (Kn→ΩKn+1 (suc n) x)))


-cancelRₖ : (n : ℕ) (x y : coHomK n) → (y +[ n ]ₖ x) -[ n ]ₖ x ≡ y
-cancelRₖ n x y = (cong (ΩKn+1→Kn n) ((cong (_∙ sym (Kn→ΩKn+1 n x)) (+ₖ→∙ n y x))
                                  ∙∙ sym (assoc _ _ _)
                                  ∙∙ cong (Kn→ΩKn+1 n y ∙_) (rCancel _)))
                   ∙∙ rCancelLem n y
                   ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) y

-cancelLₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ x ≡ y
-cancelLₖ n x y = cong (λ z → z -[ n ]ₖ x) (commₖ n x y) ∙ -cancelRₖ n x y

-+cancelₖ : (n : ℕ) (x y : coHomK n) → (x -[ n ]ₖ y) +[ n ]ₖ y ≡ x
-+cancelₖ n x y = (cong (ΩKn+1→Kn n) ((cong (_∙ (Kn→ΩKn+1 n y)) (Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ sym (Kn→ΩKn+1 n y))))
                                  ∙∙ sym (assoc _ _ _)
                                  ∙∙ cong (Kn→ΩKn+1 n x ∙_) (lCancel _)))
                   ∙∙ rCancelLem n x
                   ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) x

---- Group structure of cohomology groups ---

_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ {n = n} = sElim2 (λ _ _ → §) λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom n A → coHom n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

_-ₕ_  : {n : ℕ} → coHom n A → coHom n A → coHom n A
_-ₕ_  {n = n} = sElim2 (λ _ _ → §) λ a b → ∣ (λ x → a x -[ n ]ₖ b x) ∣₂

+ₕ-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom n A → coHom n A
-ₕ-syntax n = -ₕ_ {n = n}

-ₕ'-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
-ₕ'-syntax n = _-ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x
syntax -ₕ'-syntax n x y = x -[ n ]ₕ y

0ₕ : (n : ℕ) → coHom n A
0ₕ n = ∣ (λ _ → (0ₖ n)) ∣₂

rUnitₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (0ₕ n) ≡ x
rUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ n (a x)) i ∣₂

lUnitₕ : (n : ℕ) (x : coHom n A) → (0ₕ n) +[ n ]ₕ x ≡ x
lUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → lUnitₖ n (a x)) i ∣₂

rCancelₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (-[ n ]ₕ x) ≡ 0ₕ n
rCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ n (a x)) i ∣₂

lCancelₕ : (n : ℕ) (x : coHom n A) → (-[ n ]ₕ x) +[ n ]ₕ x  ≡ 0ₕ n
lCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ n (a x)) i ∣₂

assocₕ : (n : ℕ) (x y z : coHom n A) → ((x +[ n ]ₕ y) +[ n ]ₕ z) ≡ (x +[ n ]ₕ (y +[ n ]ₕ z))
assocₕ n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ n (a x) (b x) (c x)) i ∣₂

commₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) ≡ (y +[ n ]ₕ x)
commₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ funExt (λ x → commₖ n (a x) (b x)) i ∣₂

cancelₕ : (n : ℕ) (x : coHom n A) → x -[ n ]ₕ x ≡ 0ₕ n
cancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → cancelₖ n (a x)) i ∣₂

-ₖ-ₖ : (n : ℕ) (x : coHomK n) → (-[ n ]ₖ (-[ n ]ₖ x)) ≡ x
-ₖ-ₖ n x = cong ((ΩKn+1→Kn n) ∘ sym) (Iso.rightInv (Iso-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n x))) ∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) x

-- Proof that rUnitₖ and lUnitₖ agree on 0ₖ. Needed for Mayer-Vietoris.
rUnitlUnit0 : (n : ℕ) → rUnitₖ n (0ₖ n) ≡ lUnitₖ n (0ₖ n)
rUnitlUnit0 0 = refl
rUnitlUnit0 (suc zero) = refl
rUnitlUnit0 (suc (suc n)) = sym (rUnitlUnitGen (Iso-Kn-ΩKn+1 (2 + n)) (0ₖ (2 + n)) (Kn→ΩKn+10ₖ (2 + n)))

-cancelLₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) -[ n ]ₕ x ≡ y
-cancelLₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelLₖ n (a x) (b x) i) ∣₂

-cancelRₕ : (n : ℕ) (x y : coHom n A) → (y +[ n ]ₕ x) -[ n ]ₕ x ≡ y
-cancelRₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelRₖ n (a x) (b x) i) ∣₂

-+cancelₕ : (n : ℕ) (x y : coHom n A) → (x -[ n ]ₕ y) +[ n ]ₕ y ≡ x
-+cancelₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -+cancelₖ n (a x) (b x) i) ∣₂


-- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x) , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
+ₕ∙ (suc zero) = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ 1 ]ₖ b x) , (λ i → pa i +[ 1 ]ₖ pb i) ∙ lUnitₖ 1 (0ₖ 1) ∣₂ }
+ₕ∙ (suc (suc n)) = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (2 + n) ]ₖ b x) , (λ i → pa i +[ (2 + n) ]ₖ pb i) ∙ lUnitₖ (2 + n) (0ₖ (2 + n)) ∣₂ }

open IsSemigroup
open IsMonoid
open Group
open GroupHom
coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group
Carrier (coHomGr n A) = coHom n A
0g (coHomGr n A) = 0ₕ n
Group._+_ (coHomGr n A) x y = x +[ n ]ₕ y
Group.- (coHomGr n A) = λ x → -[ n ]ₕ x
is-set (isSemigroup (IsGroup.isMonoid (Group.isGroup (coHomGr n A)))) = §
IsSemigroup.assoc (isSemigroup (IsGroup.isMonoid (Group.isGroup (coHomGr n A)))) x y z = sym (assocₕ n x y z)
identity (IsGroup.isMonoid (Group.isGroup (coHomGr n A))) x = (rUnitₕ n x) , (lUnitₕ n x)
IsGroup.inverse (Group.isGroup (coHomGr n A)) x = (rCancelₕ n x) , (lCancelₕ n x)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)

coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma n m f' x y = sym (-cancelRₕ m (f y) (f (x -[ n ]ₕ y)))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) (sym (isHom f' (x -[ n ]ₕ y) y))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) ( cong f (-+cancelₕ n _ _))
  where
  f = fun f'

--- the loopspace of Kₙ is commutative regardless of base

addIso : (n : ℕ) (x : coHomK n) → Iso (coHomK n) (coHomK n)
fun (addIso n x) y = y +[ n ]ₖ x
inv' (addIso n x) y = y -[ n ]ₖ x
rightInv (addIso n x) y = -+cancelₖ n y x
leftInv (addIso n x) y = -cancelRₖ n x y

isCommΩK-based : (n : ℕ) (x : coHomK n) → isComm∙ (coHomK n , x)
isCommΩK-based zero x p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc zero) x =
  subst isComm∙ (λ i → coHomK 1 , lUnitₖ 1 x i)
                (ptdIso→comm {A = (_ , 0ₖ 1)} (addIso 1 x)
                              (isCommΩK 1))
isCommΩK-based (suc (suc n)) x =
  subst isComm∙ (λ i → coHomK (suc (suc n)) , lUnitₖ (suc (suc n)) x i)
                (ptdIso→comm {A = (_ , 0ₖ (suc (suc n)))} (addIso (suc (suc n)) x)
                              (isCommΩK (suc (suc n))))

addLemma : (a b : Int) → a +[ 0 ]ₖ b ≡ (a ℤ+ b)
addLemma a b = (cong (ΩKn+1→Kn 0) (sym (congFunct ∣_∣ (intLoop a) (intLoop b))))
            ∙∙ (λ i → ΩKn+1→Kn 0 (cong ∣_∣ (intLoop-hom a b i)))
            ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 0) (a ℤ+ b)

---
-- hidden versions of cohom stuff using the "lock" hack. The locked versions can be used when proving things.
-- Swapping "key" for "tt*" will then give computing functions.

Unit' : Type₀
Unit' = lockUnit {ℓ-zero}

lock : ∀ {ℓ} {A : Type ℓ} → Unit' → A → A
lock unlock = λ x → x

module lockedCohom (key : Unit') where
  +K : (n : ℕ) → coHomK n → coHomK n → coHomK n
  +K n = lock key (_+ₖ_ {n = n})

  -K : (n : ℕ) → coHomK n → coHomK n
  -K n = lock key (-ₖ_ {n = n})

  -Kbin : (n : ℕ) → coHomK n → coHomK n → coHomK n
  -Kbin n = lock key (_-ₖ_ {n = n})

  rUnitK : (n : ℕ) (x : coHomK n) → +K n x (0ₖ n) ≡ x
  rUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (0ₖ n) ≡ x
    pm unlock = rUnitₖ n x

  lUnitK : (n : ℕ) (x : coHomK n) → +K n (0ₖ n) x ≡ x
  lUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (0ₖ n) x ≡ x
    pm unlock = lUnitₖ n x

  rCancelK : (n : ℕ) (x : coHomK n) → +K n x (-K n x) ≡ 0ₖ n
  rCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (lock t (-ₖ_ {n = n}) x) ≡ 0ₖ n
    pm unlock = rCancelₖ n x

  lCancelK : (n : ℕ) (x : coHomK n) → +K n (-K n x) x ≡ 0ₖ n
  lCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (-ₖ_ {n = n}) x) x ≡ 0ₖ n
    pm unlock = lCancelₖ n x

  -cancelRK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n y x) x ≡ y
  -cancelRK n x y = pm key
    where
    pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) y x) x ≡ y
    pm unlock = -cancelRₖ n x y

  -cancelLK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n x y) x ≡ y
  -cancelLK n x y = pm key
    where
    pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) x ≡ y
    pm unlock = -cancelLₖ n x y

  -+cancelK : (n : ℕ) (x y : coHomK n) → +K n (-Kbin n x y) y ≡ x
  -+cancelK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_-ₖ_ {n = n}) x y) y ≡ x
    pm unlock = -+cancelₖ n x y

  cancelK : (n : ℕ) (x : coHomK n) → -Kbin n x x ≡ 0ₖ n
  cancelK n x = pm key
    where
    pm : (t : Unit') → (lock t (_-ₖ_ {n = n}) x x) ≡ 0ₖ n
    pm unlock = cancelₖ n x

  assocK : (n : ℕ) (x y z : coHomK n) → +K n (+K n x y) z ≡ +K n x (+K n y z)
  assocK n x y z = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) z
                     ≡ lock t (_+ₖ_ {n = n}) x (lock t (_+ₖ_ {n = n}) y z)
    pm unlock = assocₖ n x y z

  commK : (n : ℕ) (x y : coHomK n) → +K n x y ≡ +K n y x
  commK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x y ≡ lock t (_+ₖ_ {n = n}) y x
    pm unlock = commₖ n x y

  -- cohom

  +H : (n : ℕ) (x y : coHom n A) → coHom n A
  +H n = sElim2 (λ _ _ → §) λ a b → ∣ (λ x → +K n (a x) (b x)) ∣₂

  -H : (n : ℕ) (x : coHom n A) → coHom n A
  -H n = sElim (λ _ → §) λ a → ∣ (λ x → -K n (a x)) ∣₂

  -Hbin : (n : ℕ) → coHom n A → coHom n A → coHom n A
  -Hbin n = sElim2 (λ _ _ → §) (λ a b → ∣ (λ x → -Kbin n (a x) (b x)) ∣₂)

  rUnitH : (n : ℕ) (x : coHom n A) → +H n x (0ₕ n) ≡ x
  rUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → rUnitK n (a x)) i ∣₂

  lUnitH : (n : ℕ) (x : coHom n A) → +H n (0ₕ n) x ≡ x
  lUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                    λ a i → ∣ funExt (λ x → lUnitK n (a x)) i ∣₂

  rCancelH : (n : ℕ) (x : coHom n A) → +H n x (-H n x) ≡ 0ₕ n
  rCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → rCancelK n (a x)) i ∣₂

  lCancelH : (n : ℕ) (x : coHom n A) → +H n (-H n x) x  ≡ 0ₕ n
  lCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → lCancelK n (a x)) i ∣₂

  assocH : (n : ℕ) (x y z : coHom n A) → (+H n (+H n x y) z) ≡ (+H n x (+H n y z))
  assocH n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
                 λ a b c i → ∣ funExt (λ x → assocK n (a x) (b x) (c x)) i ∣₂

  commH : (n : ℕ) (x y : coHom n A) → (+H n x y) ≡ (+H n y x)
  commH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                          λ a b i → ∣ funExt (λ x → commK n (a x) (b x)) i ∣₂

  -cancelRH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n y x) x ≡ y
  -cancelRH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelRK n (a x) (b x) i) ∣₂

  -cancelLH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n x y) x ≡ y
  -cancelLH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelLK n (a x) (b x) i) ∣₂
  -+cancelH : (n : ℕ) (x y : coHom n A) → +H n (-Hbin n x y) y ≡ x
  -+cancelH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -+cancelK n (a x) (b x) i) ∣₂


+K→∙ : (key : Unit') (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (lockedCohom.+K key n a b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
+K→∙ unlock = +ₖ→∙

+H≡+ₕ : (key : Unit') (n : ℕ) → lockedCohom.+H key {A = A} n ≡ _+ₕ_ {n = n}
+H≡+ₕ unlock _ = refl

rUnitlUnit0K : (key : Unit') (n : ℕ) → lockedCohom.rUnitK key n (0ₖ n) ≡ lockedCohom.lUnitK key n (0ₖ n)
rUnitlUnit0K unlock = rUnitlUnit0
