{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.EilenbergSpaceIsoS1 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties

open import Cubical.HITs.S1 hiding (encode ; decode)
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
  F : {n : ℕ} → coHomK (suc n) → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
  F {n = n} = trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a ∙ sym (merid (ptSn (suc n))))

  F-hom : {n : ℕ} (x y : coHomK (suc n)) → F (x +ₖ y) ≡ F x ∙ F y
  F-hom {n = zero} =
    elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
          (wedgeConSn _ _
            (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
            (λ x → lUnit _
                  ∙ cong (_∙ F ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (λ y → cong F (rUnitₖ 1 ∣ y ∣)
                 ∙∙ rUnit _
                 ∙∙ cong (F ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (sym (Kn→ΩKn+1-hom-helper (F ∣ base ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))) .fst)
  F-hom {n = suc n} =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
          (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
                      (λ x → lUnit _
                            ∙ cong (_∙ F ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (λ y → cong F (rUnitₖ (2 + n) ∣ y ∣)
                           ∙∙ rUnit _
                           ∙∙ cong (F ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
                      (sym (Kn→ΩKn+1-hom-helper (F ∣ north ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))) .fst)

  F-minusDistr : {n : ℕ} (x : coHomK (suc n)) → F (-ₖ x) ≡ sym (F x)
  F-minusDistr {n = n} =
    homLemmas.distrMinus
      _+ₖ_ _∙_
      F F-hom
      (-ₖ_) sym
      ∣ (ptSn (suc n)) ∣ refl
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ (suc n)) rCancel
      assoc∙
      (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

  F-minusDistr' : {n : ℕ} (x y : coHomK (suc n)) → F (x -ₖ y) ≡ F x ∙ sym (F y)
  F-minusDistr' {n = n} =
    homLemmas.distrMinus' _+ₖ_ _∙_ F F-hom (-ₖ_) sym ∣ (ptSn (suc n)) ∣ refl
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (rUnitₖ (suc n))
      (lCancelₖ (suc n)) rCancel
      (assocₖ (suc n)) assoc∙
      (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

open Iso renaming (inv to inv')

Code' : (n : ℕ) → (S₊ (2 + n)) → Type₀
Code' n north = coHomK (suc n)
Code' n south = coHomK (suc n)
Code' n (merid a i) = isoToPath (Kₙ≃Kₙ n ∣ a ∣) i

hLevCode' : (n : ℕ) → (x : S₊ (2 + n)) → isOfHLevel (3 + n) (Code' n x)
hLevCode' n = suspToPropElim (ptSn (suc n)) (λ _ → isPropIsOfHLevel (3 + n)) (isOfHLevelTrunc (3 + n))

Code : (n : ℕ) →  coHomK (2 + n) → Type₀
Code n x = (trElim {B = λ _ → TypeOfHLevel ℓ-zero (3 + n)} (λ _ → isOfHLevelTypeOfHLevel (3 + n))
                   λ a → Code' n a , hLevCode' n a) x .fst

symMeridLem : (n : ℕ) → (x : S₊ (suc n)) (y : coHomK (suc n))
                      → subst (Code n) (cong ∣_∣ (sym (merid x))) y ≡ y -ₖ ∣ x ∣
symMeridLem n x = trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
                          (λ y → cong (_-ₖ ∣ x ∣) (transportRefl ∣ y ∣))

decode : {n : ℕ} (x : coHomK (2 + n)) → Code n x → ∣ north ∣ ≡ x
decode {n = n} = trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
                        decode-elim
  where
  north≡merid : (a : S₊ (suc n))
              → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
              ≡ (Path (coHomK (2 + n)) ∣ north ∣ ∣ south ∣)
  north≡merid a i = Path (coHomK (2 + n)) ∣ north ∣ ∣ merid a i ∣

  decode-elim : (a : S₊ (2 + n)) → Code n ∣ a ∣ → Path (coHomK (2 + n)) ∣ north ∣ ∣ a ∣
  decode-elim north = F
  decode-elim south = trRec (isOfHLevelTrunc (4 + n) _ _)
                            λ a → cong ∣_∣ (merid a)
  decode-elim (merid a i) =
    hcomp (λ k → λ { (i = i0) → F
                    ; (i = i1) → mainPath a k})
          (funTypeTransp (Code n) (λ x → ∣ north ∣ ≡ x) (cong ∣_∣ (merid a)) F i)
    where
    mainPath : (a : (S₊ (suc n))) →
           transport (north≡merid a) ∘ F ∘ transport (λ i → Code n ∣ merid a (~ i) ∣)
         ≡ trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a)
    mainPath a = funExt (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
                                (λ x → (λ i → transport (north≡merid a) (F (symMeridLem n a ∣ x ∣ i)))
                                     ∙∙ cong (transport (north≡merid a)) (-distrHelp x)
                                     ∙∙ (substAbove x)))
      where
      -distrHelp : (x : S₊ (suc n)) → F (∣ x ∣ -ₖ ∣ a ∣) ≡ cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a))
      -distrHelp x =
        F-minusDistr' ∣ x ∣ ∣ a ∣
         ∙  (λ i → (cong ∣_∣ (compPath-filler (merid x) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))
                  ∙ (cong ∣_∣ (sym (compPath-filler (merid a) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))))

      substAbove : (x : S₊ (suc n)) → transport (north≡merid a) (cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a)))
                 ≡ cong ∣_∣ (merid x)
      substAbove x i = transp (λ j → north≡merid a (i ∨ j)) i
                              (compPath-filler (cong ∣_∣ (merid x)) (λ j → ∣ merid a (~ j ∨ i) ∣) (~ i))


encode : {n : ℕ} {x : coHomK (2 + n)} → Path (coHomK (2 + n)) ∣ north ∣ x → Code n x
encode {n = n} p = transport (cong (Code n) p) ∣ (ptSn (suc n)) ∣

encode-decode : {n : ℕ} {x : coHomK (2 + n)} (p : Path (coHomK (2 + n)) ∣ north ∣ x) → decode _ (encode p) ≡ p
encode-decode {n = n} =
  J (λ y p → decode _ (encode p) ≡ p)
      (cong (decode ∣ north ∣) (transportRefl ∣ ptSn (suc n) ∣)
     ∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

stabSpheres-n≥2' : (n : ℕ) → Iso (coHomK (suc n)) (typ (Ω (coHomK-ptd (2 + n))))
fun (stabSpheres-n≥2' n) = decode _
inv' (stabSpheres-n≥2' n) = encode
rightInv (stabSpheres-n≥2' n) p = encode-decode p 
leftInv (stabSpheres-n≥2' n) =
  trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
    λ a → cong encode (congFunct ∣_∣ (merid a) (sym (merid (ptSn (suc n)))))
        ∙∙ (λ i → transport (congFunct (Code n) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid (ptSn (suc n))))) i) ∣ ptSn (suc n) ∣)
        ∙∙ (substComposite (λ x → x) (cong (Code n) (cong ∣_∣ (merid a))) (cong (Code n) (cong ∣_∣ (sym (merid (ptSn (suc n)))))) ∣ ptSn (suc n) ∣
        ∙∙ cong (transport (λ i → Code n ∣ merid (ptSn (suc n)) (~ i) ∣)) (transportRefl (∣ a ∣ +ₖ ∣ (ptSn (suc n)) ∣) ∙ rUnitₖ (suc n) ∣ a ∣)
        ∙∙ symMeridLem n (ptSn (suc n)) ∣ a ∣
        ∙∙ cong (∣ a ∣ +ₖ_) -0ₖ
        ∙∙ rUnitₖ (suc n) ∣ a ∣)
