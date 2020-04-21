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
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool

open import Cubical.ZCohomology.cupProdPrelims

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


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
    map1 f = map1' , refl module helpmap where
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
Kn→ΩKn+1 n = Iso.fun (Iso2-Kn-ΩKn+1 n)

ΩKn+1→Kn : {n : ℕ} → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn {n = n} = Iso.inv (Iso2-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)


---------- Algebra --------

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = n} x y  = ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)

-ₖ_ : {n : ℕ} → coHomK n → coHomK n
-ₖ_ {n = n} x = ΩKn+1→Kn (sym (Kn→ΩKn+1 n x))

0ₖ : {n : ℕ} → coHomK n
0ₖ {n = zero} = pt (coHomK-ptd 0)
0ₖ {n = suc n} = pt (coHomK-ptd (suc n))

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n 0ₖ ≡ refl
Kn→ΩKn+10ₖ zero = refl
Kn→ΩKn+10ₖ (suc n) = (λ i → cong ∣_∣ (rCancel (merid north) i))


rUnitₖ : {n : ℕ} (x : coHomK n) → x +ₖ 0ₖ ≡ x
rUnitₖ {n = zero} x = cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso2-Kn-ΩKn+1 zero) x
rUnitₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) x ∙ Kn→ΩKn+10ₖ (suc n) i)) ∙
                       (λ i → ΩKn+1→Kn (rUnit (Kn→ΩKn+1 (suc n) x) (~ i))) ∙
                       Iso.leftInv (Iso2-Kn-ΩKn+1 (suc n)) x

lUnitₖ : {n : ℕ} (x : coHomK n) → 0ₖ +ₖ x ≡ x
lUnitₖ {n = zero} x = cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso2-Kn-ΩKn+1 zero) x
lUnitₖ {n = suc n} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) x)) ∙
                       (λ i → ΩKn+1→Kn (lUnit (Kn→ΩKn+1 (suc n) x) (~ i))) ∙
                       Iso.leftInv (Iso2-Kn-ΩKn+1 (suc n)) x

rCancelₖ  : {n : ℕ} (x : coHomK n) → x +ₖ (-ₖ x) ≡ 0ₖ
rCancelₖ {n = zero} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 zero x ∙ Iso.rightInv (Iso2-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i)) ∙
                        cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 zero x))
rCancelₖ {n = suc zero} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 1 x ∙ Iso.rightInv (Iso2-Kn-ΩKn+1 1) (sym (Kn→ΩKn+1 1 x)) i)) ∙
                            cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 1 x))
rCancelₖ {n = suc (suc n)} x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (2 + n) x ∙ Iso.rightInv (Iso2-Kn-ΩKn+1 (2 + n)) (sym (Kn→ΩKn+1 (2 + n) x)) i)) ∙
                               cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 (2 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc (suc n)) (~ i))) ∙
                               Iso.leftInv (Iso2-Kn-ΩKn+1 (suc (suc n))) 0ₖ

lCancelₖ : {n : ℕ} (x : coHomK n) → (-ₖ x) +ₖ x  ≡ 0ₖ
lCancelₖ {n = zero} x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso2-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i ∙ Kn→ΩKn+1 zero x)) ∙
                        cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 zero x))
lCancelₖ {n = suc zero} x = ((λ i → ΩKn+1→Kn (Iso.rightInv (Iso2-Kn-ΩKn+1 1) (sym (Kn→ΩKn+1 1 x)) i ∙ Kn→ΩKn+1 1 x))) ∙
                            cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 1 x))
lCancelₖ {n = suc (suc n)} x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso2-Kn-ΩKn+1 (2 + n)) (sym (Kn→ΩKn+1 (2 + n) x)) i ∙ Kn→ΩKn+1 (2 + n) x)) ∙
                               cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 (2 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc (suc n)) (~ i))) ∙
                               Iso.leftInv (Iso2-Kn-ΩKn+1 (suc (suc n))) 0ₖ


assocₖ : {n : ℕ} (x y z : coHomK n) → ((x +ₖ y) +ₖ z) ≡ (x +ₖ (y +ₖ z)) 
assocₖ {n = n} x y z = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 n (ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)) ∙ Kn→ΩKn+1 n z)) ∙
                          (λ i → ΩKn+1→Kn (Iso.rightInv (Iso2-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i ∙ Kn→ΩKn+1 n z)) ∙
                          (λ i → ΩKn+1→Kn (assoc (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) (Kn→ΩKn+1 n z) (~ i))) ∙
                          (λ i → ΩKn+1→Kn ((Kn→ΩKn+1 n x) ∙ Iso.rightInv (Iso2-Kn-ΩKn+1 n) ((Kn→ΩKn+1 n y ∙ Kn→ΩKn+1 n z)) (~ i)))

commₖ : {n : ℕ} (x y : coHomK n) → (x +ₖ y) ≡ (y +ₖ x)
commₖ {n = n} x y i = ΩKn+1→Kn (EH-instance (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i)
  where
  EH-instance : (p q : typ (Ω ((∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) , ∣ north ∣))) → p ∙ q ≡ q ∙ p
  EH-instance = transport (λ i → (p q : K-Id n (~ i)) → p ∙ q ≡ q ∙ p)
                          λ p q → Eckmann-Hilton 0 p q
    where
    K-Id : (n : ℕ) → typ (Ω (hLevelTrunc (3 + n) (S₊ (1 + n)) , ∣ north ∣)) ≡ typ ((Ω^ 2) (hLevelTrunc (4 + n) (S₊ (2 + n)) , ∣  north ∣ ))
    K-Id n = (λ i → typ (Ω (isoToPath (Iso2-Kn-ΩKn+1 (suc n)) i , hcomp (λ k → λ {(i = i0) → ∣ north ∣
                                                                                  ; (i = i1) → transportRefl (λ j → ∣ rCancel (merid north) k j ∣) k})
                                                                         (transp (λ j → isoToPath (Iso2-Kn-ΩKn+1 (suc n)) (i ∧ j)) (~ i)  ∣ north ∣))))
