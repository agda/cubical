{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Properties where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Group.Base hiding (_≃_ ; Iso)
open import Cubical.Data.Group.GroupLibrary


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)

open import Cubical.ZCohomology.KcompPrelims

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ


{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                 (A : Set ℓ) →
                 (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₀
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

coHomRed+1Equiv (suc n) A i = ∥ coHomRed+1.helpLemma A i {C = ((coHomK (suc n)) , ∣ north ∣)} i ∥₀

-----------

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso3-Kn-ΩKn+1 n)

ΩKn+1→Kn : {n : ℕ} → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn {n = n} = Iso.inv (Iso3-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

---------- Algebra/Group stuff --------

0ₖ : {n : ℕ} → coHomK n
0ₖ {n = zero} = pt (coHomK-ptd 0)
0ₖ {n = suc n} = pt (coHomK-ptd (suc n))

infixr 35 _+ₖ_

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = n} x y  = ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)

-ₖ_ : {n : ℕ} → coHomK n → coHomK n
-ₖ_ {n = n} x = ΩKn+1→Kn (sym (Kn→ΩKn+1 n x))

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n 0ₖ ≡ refl
Kn→ΩKn+10ₖ zero = refl
Kn→ΩKn+10ₖ (suc n) = (λ i → cong ∣_∣ (rCancel (merid north) i)) -- could also use refl for n = 1, but for computational reasons I don't want to expand the definition if not necessary.

-0ₖ : {n : ℕ} → -ₖ 0ₖ {n = n} ≡ 0ₖ
-0ₖ {n = n} = (λ i → ΩKn+1→Kn (sym (Kn→ΩKn+10ₖ n i)))
            ∙∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ n (~ i)))
            ∙∙ Iso.leftInv (Iso3-Kn-ΩKn+1 n) 0ₖ



-- cong-ₖ : {n : ℕ} (x : coHomK n) → PathP (λ i → -0ₖ {n = (suc n)} i ≡ -0ₖ i) (cong -ₖ_ (Kn→ΩKn+1 n x)) (Kn→ΩKn+1 n (-ₖ x))
-- cong-ₖ {n = n} x j i =
--   hcomp (λ k → λ{ (i = i0) → -0ₖ j
--                  ; (i = i1) → -0ₖ j
--                  ; (j = i0) → ΩKn+1→Kn (sym (Kn→ΩKn+1 (suc n) (Kn→ΩKn+1 n x i)))
--                  ; (j = i1) → Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n x)) (~ k) i})
--         (hcomp (λ k → λ{ (j = i0) → {!!}
--                         ; (j = i1) → {!!}})
--                {!!})
-- {-
-- j = i0 ⊢ ΩKn+1→Kn (sym (Kn→ΩKn+1 (suc n) (Kn→ΩKn+1 n x i)))
-- j = i1 ⊢ Kn→ΩKn+1 x (~ i) -- Kn→ΩKn+1 n (-ₖ x) i
-- i = i0 ⊢ -0ₖ j
-- i = i1 ⊢ -0ₖ j
-- -}

+ₖ→∙ : (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (a +ₖ b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
+ₖ→∙ n a b = Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b)

commₖ : {n : ℕ} (x y : coHomK n) → (x +ₖ y) ≡ (y +ₖ x)
commₖ {n = n} x y i = ΩKn+1→Kn (EH-instance (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i)
  where
  EH-instance : (p q : typ (Ω ((∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) , ∣ north ∣))) → p ∙ q ≡ q ∙ p
  EH-instance = transport (λ i → (p q : K-Id n (~ i)) → p ∙ q ≡ q ∙ p)
                          λ p q → Eckmann-Hilton 0 p q
    where
    K-Id : (n : ℕ) → typ (Ω (hLevelTrunc (3 + n) (S₊ (1 + n)) , ∣ north ∣)) ≡ typ ((Ω^ 2) (hLevelTrunc (4 + n) (S₊ (2 + n)) , ∣  north ∣ ))
    K-Id n = (λ i → typ (Ω (isoToPath (Iso3-Kn-ΩKn+1 (suc n)) i , hcomp (λ k → λ { (i = i0) → ∣ north ∣
                                                                                  ;  (i = i1) → transportRefl (λ j → ∣ rCancel (merid north) k j ∣) k})
                                                                         (transp (λ j → isoToPath (Iso3-Kn-ΩKn+1 (suc n)) (i ∧ j)) (~ i)  ∣ north ∣))))

lUnitₖ : {n : ℕ} (x : coHomK n) → 0ₖ +ₖ x ≡ x
lUnitₖ {n = zero} x = cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso3-Kn-ΩKn+1 zero) x
lUnitₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) x)) ∙
                       (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) x)))) ∙
                       Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) x

rUnitₖ : {n : ℕ} (x : coHomK n) → x +ₖ 0ₖ ≡ x
rUnitₖ {n = zero} x = cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso3-Kn-ΩKn+1 zero) x
rUnitₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) x ∙ Kn→ΩKn+10ₖ (suc n) i)) ∙
                       (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) x)))) ∙
                       Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) x
-- 


rUnitₖ' : {n : ℕ} (x : coHomK n) → x +ₖ 0ₖ ≡ x
rUnitₖ' {n = n} x = commₖ x 0ₖ ∙ lUnitₖ x

rCancelₖ  : {n : ℕ} (x : coHomK n) → x +ₖ (-ₖ x) ≡ 0ₖ
rCancelₖ {n = zero} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 zero x ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i)) ∙
                        cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 zero x))
rCancelₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (1 + n) x ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i)) ∙
                               cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) 0ₖ

lCancelₖ : {n : ℕ} (x : coHomK n) → (-ₖ x) +ₖ x  ≡ 0ₖ
lCancelₖ {n = zero} x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i ∙ Kn→ΩKn+1 zero x)) ∙
                        cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 zero x))
lCancelₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i ∙ Kn→ΩKn+1 (1 + n) x)) ∙
                               cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) 0ₖ


assocₖ : {n : ℕ} (x y z : coHomK n) → ((x +ₖ y) +ₖ z) ≡ (x +ₖ (y +ₖ z))
assocₖ {n = n} x y z = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 n (ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)) ∙ Kn→ΩKn+1 n z)) ∙
                          (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i ∙ Kn→ΩKn+1 n z)) ∙
                          (λ i → ΩKn+1→Kn (assoc (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) (Kn→ΩKn+1 n z) (~ i))) ∙
                          (λ i → ΩKn+1→Kn ((Kn→ΩKn+1 n x) ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 n) ((Kn→ΩKn+1 n y ∙ Kn→ΩKn+1 n z)) (~ i)))


-distrₖ : {n : ℕ} → (x y : coHomK n) → -ₖ (x +ₖ y) ≡ (-ₖ x) +ₖ (-ₖ y)
-distrₖ {n = n} x y = (λ i → ΩKn+1→Kn (sym (Kn→ΩKn+1 n (ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y))))) ∙
                      (λ i → ΩKn+1→Kn (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i))) ∙
                      (λ i → ΩKn+1→Kn (symDistr (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i)) ∙
                      (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n y)) (~ i) ∙ (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n x)) (~ i)))) ∙
                      commₖ (-ₖ y) (-ₖ x)


-- Group structure of cohomology groups ---


private
  § : isSet ∥ A ∥₀
  § = setTruncIsSet

_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ = sElim2 (λ _ _ → §) λ a b → ∣ (λ x → a x +ₖ b x) ∣₀

-ₕ  : {n : ℕ} → coHom n A → coHom n A
-ₕ  = sRec § λ a → ∣ (λ x → -ₖ a x) ∣₀

0ₕ : {n : ℕ} → coHom n A
0ₕ = ∣ (λ _ → 0ₖ) ∣₀

rUnitₕ : {n : ℕ} (x : coHom n A) → x +ₕ 0ₕ ≡ x
rUnitₕ  = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ (a x)) i ∣₀

lUnitₕ : {n : ℕ} (x : coHom n A) → 0ₕ +ₕ x ≡ x
lUnitₕ = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
               λ a i → ∣ funExt (λ x → lUnitₖ (a x)) i ∣₀

rCancelₕ : {n : ℕ} (x : coHom n A) → x +ₕ (-ₕ x) ≡ 0ₕ
rCancelₕ = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ (a x)) i ∣₀

lCancelₕ : {n : ℕ} (x : coHom n A) → (-ₕ x) +ₕ x  ≡ 0ₕ
lCancelₕ = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ (a x)) i ∣₀

assocₕ : {n : ℕ} (x y z : coHom n A) → ((x +ₕ y) +ₕ z) ≡ (x +ₕ (y +ₕ z))
assocₕ = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ (a x) (b x) (c x)) i ∣₀

commₕ : {n : ℕ} (x y : coHom n A) → (x +ₕ y) ≡ (y +ₕ x)
commₕ {n = n} = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                       λ a b i → ∣ funExt (λ x → commₖ (a x) (b x)) i ∣₀


rUnitlUnit0 : {n : ℕ} → rUnitₖ {n = n} 0ₖ  ≡ lUnitₖ 0ₖ
rUnitlUnit0 {n = zero} = refl
rUnitlUnit0 {n = suc n} =
  (assoc (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) 0ₖ ∙ Kn→ΩKn+10ₖ (suc n) i))
         (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) 0ₖ))))
         (Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) 0ₖ))
 ∙ (λ j → helper j
         ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) 0ₖ)
 ∙ sym (assoc (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) 0ₖ)) (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) 0ₖ)))) (Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) 0ₖ))

  where
  helper : (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) 0ₖ ∙ Kn→ΩKn+10ₖ (suc n) i))
          ∙ (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) 0ₖ))))
          ≡ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) 0ₖ))
          ∙ (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) 0ₖ))))
  helper = (λ j → lUnit (rUnit ((λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) 0ₖ ∙ Kn→ΩKn+10ₖ (suc n) i))) j) j
                   ∙ rUnit (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) 0ₖ)))) j)
         ∙ (λ j → ((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣ ∙ (λ i → ∣ rCancel (merid north) (z ∧ j) i ∣)))
                 ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) 0ₖ ∙ Kn→ΩKn+10ₖ (suc n) (i ∨ j)))
                 ∙ λ z → ΩKn+1→Kn (((λ i → ∣ rCancel (merid north) (z ∧ j) i ∣)) ∙ refl))
                 ∙ cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+10ₖ (suc n) j)))
                 ∙ λ z → ΩKn+1→Kn (λ i → ∣ rCancel (merid north) ((~ z) ∧ j) i ∣))
         ∙ (λ j → (((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣ ∙ (λ i → ∣ rCancel (merid north) z i ∣))))
                  ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) 0ₖ ∙ refl))
                  ∙ λ z → ΩKn+1→Kn ((λ i → ∣ rCancel (merid north) z i ∣) ∙ λ i → ∣ rCancel (merid north) ((~ z) ∨ (~ j)) i ∣))
                 ∙ cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+10ₖ (suc n) (~ j))))
                 ∙ λ z → ΩKn+1→Kn (λ i → ∣ rCancel (merid north) (~ z ∧ (~ j)) i ∣))
         ∙ (λ j → ((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣  ∙ λ i → ∣ rCancel (merid north) (z ∧ (~ j)) i ∣))
                  ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (i ∧ j) ∙ Kn→ΩKn+10ₖ (suc n) (~ j)))
                  ∙ λ z → ΩKn+1→Kn ((λ i → ∣ rCancel (merid north) (z ∨ j) i ∣) ∙ λ i → ∣ rCancel (merid north) (~ z ∧ ~ j) i ∣))
                 ∙ rUnit (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) 0ₖ)))) (~ j))
         ∙ (λ j → lUnit (rUnit (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) 0ₖ)) (~ j)) (~ j)
                 ∙ cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) 0ₖ))))



---- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +ₖ b x) , (λ i → (pa i +ₖ pb i)) ∣₀ } -- ∣ (λ x → a x +ₖ b x) ∣₀
+ₕ∙ (suc n) = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +ₖ b x) , (λ i → pa i +ₖ pb i) ∙ lUnitₖ 0ₖ ∣₀ }


-ₕ∙  : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A
-ₕ∙ zero = sRec § λ {(a , pt) → ∣ (λ x → -ₖ a x ) , (λ i → -ₖ (pt i)) ∣₀}
-ₕ∙ (suc n) = sRec § λ {(a , pt) → ∣ (λ x → -ₖ a x ) , (λ i → -ₖ (pt i)) ∙
                                                                 (λ i → ΩKn+1→Kn (sym (Kn→ΩKn+10ₖ (suc n) i))) ∙
                                                                 (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                                                                 Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) ∣ north ∣ ∣₀}

0ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A
0ₕ∙ zero = ∣ (λ _ → 0ₖ) , refl ∣₀
0ₕ∙ (suc n) = ∣ (λ _ → 0ₖ) , refl ∣₀



module _ {A : Type ℓ} {A' : Pointed ℓ'} (n : ℕ) where
  0prod : coHomRed n A' × coHom n A
  0prod = (0ₕ∙ n) , 0ₕ

  -prod : coHomRed n A' × coHom n A → coHomRed n A' × coHom n A
  -prod (a , b) = (-ₕ∙ n a) , (-ₕ b)

  +prod : coHomRed n A' × coHom n A → coHomRed n A' × coHom n A → coHomRed n A' × coHom n A
  +prod (a , b) (c , d) = (+ₕ∙ n a c) , (b +ₕ d)



coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group ℓ
Group.type (coHomGr n A) = coHom n A
Group.setStruc (coHomGr n A) = §
isGroup.id (Group.groupStruc (coHomGr n A)) = 0ₕ
isGroup.inv (Group.groupStruc (coHomGr n A)) = -ₕ
isGroup.comp (Group.groupStruc (coHomGr n A)) = _+ₕ_
isGroup.lUnit (Group.groupStruc (coHomGr n A)) = lUnitₕ
isGroup.rUnit (Group.groupStruc (coHomGr n A)) = rUnitₕ
isGroup.assoc (Group.groupStruc (coHomGr n A)) = assocₕ
isGroup.lCancel (Group.groupStruc (coHomGr n A)) = lCancelₕ
isGroup.rCancel (Group.groupStruc (coHomGr n A)) = rCancelₕ

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group (ℓ-max ℓ ℓ')
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)
