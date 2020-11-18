{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.EilenbergSpaceIso where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Nat renaming (+-assoc to +-assocℕ ; +-comm to +-commℕ)
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3 ; map2 to trMap2)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Freudenthal
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Data.HomotopyGroup

open import Cubical.ZCohomology.GroupStructure

open Iso renaming (inv to inv')

module homLemmas {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
         (_+A_ : A → A → A) (_+B_ : B → B → B)
         (f : A → B) (f-hom : (x y : A) → f (x +A y) ≡ f x +B f y)
          where
  distrMinus : (-A_ : A → A) (-B : B → B) (a₀ : A) (b₀ : B)
               (lUnitB : (x : B) → b₀ +B x ≡ x)
               (rUnitB : (x : B) → x +B b₀ ≡ x)
               (lCancelA : (x : A) → (-A x) +A x ≡ a₀)
               (rCancelB : (x : B) → x +B (-B x) ≡ b₀)
               (assocB : (x y z : B) → x +B (y +B z) ≡ ((x +B y) +B z))
               (0↦0 : f a₀ ≡ b₀)
               (x : A) → f (-A x) ≡ -B (f x)
  distrMinus -A_ -B_ a₀ b₀ lUnitB rUnitB lCancelA rCancelB assocB 0↦0 x =
       sym (rUnitB _)
    ∙∙ cong (f (-A x) +B_) (sym (rCancelB (f x)))
    ∙∙ assocB _ _ _
    ∙∙ cong (_+B (-B (f x))) (sym (f-hom (-A x) x) ∙∙ cong f (lCancelA x) ∙∙ 0↦0)
    ∙∙ lUnitB _

  distrMinus' : (-A_ : A → A) (-B : B → B) (a₀ : A) (b₀ : B)
                (lUnitB : (x : B) → b₀ +B x ≡ x)
                (rUnitB : (x : B) → x +B b₀ ≡ x)
                (rUnitA : (x : A) → x +A a₀ ≡ x)
                (lCancelA : (x : A) → (-A x) +A x ≡ a₀)
                (rCancelB : (x : B) → x +B (-B x) ≡ b₀)
                (assocA : (x y z : A) → x +A (y +A z) ≡ ((x +A y) +A z))
                (assocB : (x y z : B) → x +B (y +B z) ≡ ((x +B y) +B z))
                (0↦0 : f a₀ ≡ b₀)
                (x y : A)
             → f (x +A (-A y)) ≡ (f x +B (-B (f y)))
  distrMinus' -A_ -B_ a₀ b₀ lUnitB rUnitB rUnitA lCancelA rCancelB assocA assocB 0↦0 x y =
       sym (rUnitB _)
    ∙∙ cong (f (x +A (-A y)) +B_) (sym (rCancelB (f y))) ∙ assocB _ _ _
    ∙∙ cong (_+B (-B f y)) (sym (f-hom (x +A (-A y)) y) ∙ cong f (sym (assocA x (-A y) y) ∙∙ cong (x +A_) (lCancelA y) ∙∙ rUnitA x))

Kₙ≃Kₙ : (n : ℕ) (x : coHomK (suc n)) → Iso (coHomK (suc n)) (coHomK (suc n))
fun (Kₙ≃Kₙ n x) y = x +ₖ y
inv' (Kₙ≃Kₙ n x) y = y -ₖ x
rightInv (Kₙ≃Kₙ n x) y = commₖ (suc n) x (y -ₖ x) ∙ -+cancelₖ (suc n) y x
leftInv (Kₙ≃Kₙ n x) y = -cancelLₖ (suc n) x y


private

  F : {n : ℕ} → coHomK (2 + n) → Path (coHomK (3 + n)) ∣ north ∣ ∣ north ∣
  F {n = n} = trRec (isOfHLevelTrunc (5 + n) _ _) λ a → cong ∣_∣ ((merid a) ∙ sym (merid north))

  F-hom : {n : ℕ} (x y : coHomK (2 + n)) → F (x +ₖ y) ≡ F x ∙ F y
  F-hom {n = n} =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
          (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
                      (λ x → lUnit _ ∙ cong (_∙ F ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (λ y →  cong F (rUnitₖ (2 + n) ∣ y ∣)
                            ∙∙ rUnit _
                            ∙∙ cong (F ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (sym (Kn→ΩKn+1-hom-helper (F ∣ north ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))) .fst)

  F-minusDistr : {n : ℕ} (x : coHomK (2 + n)) → F (-ₖ x) ≡ sym (F x)
  F-minusDistr {n = n} =
    homLemmas.distrMinus
      _+ₖ_ _∙_
      F F-hom
      (-ₖ_) sym
      ∣ north ∣ refl
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ (2 + n)) rCancel
      assoc∙
      (cong (cong ∣_∣) (rCancel (merid north)))

  F-minusDistr' : {n : ℕ} (x y : coHomK (2 + n)) → F (x -ₖ y) ≡ F x ∙ sym (F y)
  F-minusDistr' {n = n} =
    homLemmas.distrMinus' _+ₖ_ _∙_ F F-hom (-ₖ_) sym ∣ north ∣ refl
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (rUnitₖ (2 + n))
      (lCancelₖ (2 + n)) rCancel
      (assocₖ (2 + n)) assoc∙
      ((cong (cong ∣_∣) (rCancel (merid north))))

CODE : (n : ℕ) → (S₊ (3 + n)) → Type₀
CODE n north = hLevelTrunc (4 + n) (S₊ (2 + n))
CODE n south = hLevelTrunc (4 + n) (S₊ (2 + n))
CODE n (merid a i) = isoToPath (Kₙ≃Kₙ (suc n) ∣ a ∣) i

hLevCode : (n : ℕ) (x : S₊ (3 + n)) → isOfHLevel (4 + n) (CODE n x)
hLevCode n = suspToPropElim north (λ _ → isPropIsOfHLevel (4 + n)) (isOfHLevelTrunc (4 + n))

CODEs : (n : ℕ) → hLevelTrunc (5 + n) (S₊ (3 + n)) → Type₀
CODEs n x = (trElim {B = λ _ → TypeOfHLevel ℓ-zero (4 + n)} (λ _ → isOfHLevelTypeOfHLevel (4 + n))
                         λ a → CODE n a , hLevCode n a) x .fst

funTransp : ∀ {ℓ ℓ'} {A : Type ℓ} {B C : A → Type ℓ'} {x y : A} (p : x ≡ y) (f : B x → C x)
         → PathP (λ i → B (p i) → C (p i)) f (subst C p ∘ f ∘ subst B (sym p))
funTransp {B = B} {C = C} {x = x} p f i b = transp (λ j → C (p (j ∧ i))) (~ i) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b))

transport-ua⁻ : ∀ {ℓ} {A B : Type ℓ} (e : Iso A B) (x : B) → transport (sym (isoToPath e)) x ≡ inv' e x
transport-ua⁻ e x = cong (inv' e) (transportRefl x)

symMeridLem : (n : ℕ) (x : S₊ (2 + n)) (y : coHomK (2 + n)) → subst (CODEs n) (cong ∣_∣ (sym (merid x))) y ≡ y -ₖ ∣ x ∣
symMeridLem n x = trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
                             λ y → (λ i → transport (sym (isoToPath (Kₙ≃Kₙ (suc n) ∣ x ∣))) ∣ y ∣)
                                   ∙ transport-ua⁻ (Kₙ≃Kₙ (suc n) ∣ x ∣) ∣ y ∣

dec : (n : ℕ) (x : hLevelTrunc (5 + n) (S₊ (3 + n))) → CODEs n x → ∣ north ∣ ≡ x
dec n = trElim (λ _ → isOfHLevelΠ (5 + n) λ _ → isOfHLevelPath (5 + n) (isOfHLevelTrunc (5 + n)) _ _)
               decode-elim
  where
  north≡merid : (a : Susp (S₊ (suc n)))
              → Path (hLevelTrunc (5 + n) (S₊ (3 + n))) ∣ north ∣ ∣ north ∣
              ≡ (Path (hLevelTrunc (5 + n) (S₊ (3 + n))) ∣ north ∣ ∣ south ∣)
  north≡merid a i = Path (hLevelTrunc (5 + n) (S₊ (3 + n))) ∣ north ∣ ∣ merid a i ∣

  decode-elim : (a : Susp (Susp (S₊ (suc n)))) → CODEs n ∣ a ∣ → ∣ north ∣ ≡ ∣ a ∣
  decode-elim north = F
  decode-elim south = trRec (isOfHLevelTrunc (5 + n) _ _)
                     λ a → cong ∣_∣ (merid a)
  decode-elim (merid a i) =
    hcomp (λ k → λ {(i = i0) → F
                   ; (i = i1) → help2 a k})
          (funTransp {B = CODEs n} {C = λ x → ∣ north ∣ ≡ x} (λ i → ∣ merid a i ∣) F i)
    where
    help : (a x : (Susp (S₊ (suc n))))
        → (transport (north≡merid a) ∘ F ∘ transport (λ i → CODEs n ∣ merid a (~ i) ∣)) ∣ x ∣
         ≡ cong ∣_∣ (merid x)
    help a x =
             (λ i → transport (north≡merid a)
                        (F (symMeridLem n a ∣ x ∣ i)))
           ∙∙ (cong (transport (north≡merid a)) -distrHelp)
           ∙∙ substAbove
      where
      -distrHelp : F (∣ x ∣ -ₖ ∣ a ∣)
            ≡ cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a))
      -distrHelp = F-minusDistr' ∣ x ∣ ∣ a ∣
               ∙  (λ i → (cong ∣_∣ (compPath-filler (merid x) (λ j → merid north (~ j ∨ i)) (~ i)))
                        ∙ (cong ∣_∣ (sym (compPath-filler (merid a) (λ j → merid north (~ j ∨ i)) (~ i)))))

      substAbove : transport (north≡merid a) (cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a)))
                 ≡ cong ∣_∣ (merid x)
      substAbove = (λ i → transp (λ j → north≡merid a (i ∨ j)) i (cong ∣_∣ (merid x) ∙ cong ∣_∣ λ j → merid a (~ j ∨ i)))
                  ∙ sym (rUnit _)

    help2 : (a : (Susp (S₊ (suc n)))) →
           transport (north≡merid a) ∘ F ∘ transport (λ i → CODEs n ∣ merid a (~ i) ∣)
         ≡ trRec (isOfHLevelTrunc (5 + n) _ _) λ a → cong ∣_∣ (merid a)
    help2 a = funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
                     (help a))

encoder : (n : ℕ) (x : coHomK (3 + n)) → Path (coHomK (3 + n)) ∣ north ∣ x → CODEs n x
encoder n x p = transport (cong (CODEs n) p) ∣ north ∣

encode-decode : (n : ℕ) → (x : coHomK (3 + n)) (p : Path (coHomK (3 + n)) ∣ north ∣ x) → dec n _ (encoder n x p) ≡ p
encode-decode n x = J (λ x p → dec n _ (encoder n x p) ≡ p) (cong (dec n ∣ north ∣) (transportRefl ∣ north ∣) ∙ cong (cong ∣_∣) (rCancel (merid north)))

stabSpheres-n≥2' : (n : ℕ) → Iso (coHomK (2 + n)) (typ (Ω (coHomK-ptd (3 + n))))
fun (stabSpheres-n≥2' n) = dec n ∣ north ∣
inv' (stabSpheres-n≥2' n) = encoder n ∣ north ∣
rightInv (stabSpheres-n≥2' n) p = encode-decode n ∣ north ∣ p 
leftInv (stabSpheres-n≥2' n) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
    λ a → cong (encoder n ∣ north ∣) (congFunct ∣_∣ (merid a) (sym (merid north)))
        ∙∙ (λ i → transport (congFunct (CODEs n) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid north))) i) ∣ north ∣)
        ∙∙ (substComposite (λ x → x) (cong (CODEs n) (cong ∣_∣ (merid a))) (cong (CODEs n) (cong ∣_∣ (sym (merid north)))) ∣ north ∣
        ∙∙ cong (transport (λ i → CODEs n ∣ merid north (~ i) ∣)) (transportRefl (∣ a ∣ +ₖ ∣ north ∣) ∙ rUnitₖ (2 + n) ∣ a ∣)
        ∙∙ (symMeridLem n north ∣ a ∣
         ∙ rUnitₖ (2 + n) ∣ a ∣))

