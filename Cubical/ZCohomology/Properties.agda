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
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint


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
coHomRed+1Equiv (suc n) A i = ∥ coHomRed+1.helpLemma A i {C = ((coHomK (suc n)) , ∣ north ∣)} i ∥₂

-----------

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso3-Kn-ΩKn+1 n)

ΩKn+1→Kn : {n : ℕ} → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn {n = n} = Iso.inv (Iso3-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso3-Kn-ΩKn+1 n)

---------- Algebra/Group stuff --------

0ₖ : (n : ℕ) → coHomK n
0ₖ zero = pt (coHomK-ptd 0)
0ₖ (suc n) = pt (coHomK-ptd (suc n))

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = n} x y  = ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)

-ₖ_ : {n : ℕ} → coHomK n → coHomK n
-ₖ_ {n = n} x = ΩKn+1→Kn (sym (Kn→ΩKn+1 n x))

+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = refl
Kn→ΩKn+10ₖ (suc n) i j = ∣ (rCancel (merid north) i j) ∣

-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ {n = n} = (λ i → ΩKn+1→Kn (sym (Kn→ΩKn+10ₖ n i)))
            ∙∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ n (~ i)))
            ∙∙ Iso.leftInv (Iso3-Kn-ΩKn+1 n) (0ₖ n)

+ₖ→∙ : (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (a +[ n ]ₖ b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
+ₖ→∙ n a b = Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b)

lUnitₖ : (n : ℕ) (x : coHomK n) → (0ₖ n) +[ n ]ₖ x ≡ x
lUnitₖ 0 x = cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso3-Kn-ΩKn+1 zero) x
lUnitₖ (suc n) x = (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) x)) ∙
                       (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) x)))) ∙
                       Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) x

rUnitₖ : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ 0 x = cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 zero x))) ∙
                      Iso.leftInv (Iso3-Kn-ΩKn+1 zero) x
rUnitₖ (suc n) x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) x ∙ Kn→ΩKn+10ₖ (suc n) i)) ∙
                       (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) x)))) ∙
                       Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) x
--

rCancelₖ  : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (-[ n ]ₖ x) ≡ (0ₖ n)
rCancelₖ zero x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 zero x ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i)) ∙
                        cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 zero x))
rCancelₖ (suc n) x = (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (1 + n) x ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i)) ∙
                               cong ΩKn+1→Kn (rCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))

lCancelₖ : (n : ℕ) (x : coHomK n) → (-[ n ]ₖ x) +[ n ]ₖ x  ≡ (0ₖ n)
lCancelₖ 0 x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 zero) (sym (Kn→ΩKn+1 zero x)) i ∙ Kn→ΩKn+1 zero x)) ∙
                        cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 zero x))
lCancelₖ (suc n) x = (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 (1 + n)) (sym (Kn→ΩKn+1 (1 + n) x)) i ∙ Kn→ΩKn+1 (1 + n) x)) ∙
                               cong ΩKn+1→Kn (lCancel (Kn→ΩKn+1 (1 + n) x)) ∙
                               (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                               Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))

assocₖ : (n : ℕ) (x y z : coHomK n) → ((x +[ n ]ₖ y) +[ n ]ₖ z) ≡ (x +[ n ]ₖ (y +[ n ]ₖ z))
assocₖ n x y z = ((λ i → ΩKn+1→Kn (Kn→ΩKn+1 n (ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y)) ∙ Kn→ΩKn+1 n z)) ∙∙
                          (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i ∙ Kn→ΩKn+1 n z)) ∙∙
                          (λ i → ΩKn+1→Kn (assoc (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) (Kn→ΩKn+1 n z) (~ i)))) ∙
                          (λ i → ΩKn+1→Kn ((Kn→ΩKn+1 n x) ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 n) ((Kn→ΩKn+1 n y ∙ Kn→ΩKn+1 n z)) (~ i)))

commₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) ≡ (y +[ n ]ₖ x)
commₖ n x y i = ΩKn+1→Kn (EH-instance (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i)
  where
  EH-instance : (p q : typ (Ω ((∥ S₊ (suc n) ∥ (2 + (suc n))) , ∣ north ∣))) → p ∙ q ≡ q ∙ p
  EH-instance = transport (λ i → (p q : K-Id n (~ i)) → p ∙ q ≡ q ∙ p)
                          λ p q → Eckmann-Hilton 0 p q
    where
    K-Id : (n : HLevel) → typ (Ω (hLevelTrunc (3 + n) (S₊ (1 + n)) , ∣ north ∣)) ≡ typ ((Ω^ 2) (hLevelTrunc (4 + n) (S₊ (2 + n)) , ∣  north ∣ ))
    K-Id n = (λ i → typ (Ω (isoToPath (Iso2-Kn-ΩKn+1 (suc n)) i , hcomp (λ k → λ { (i = i0) → ∣ north ∣
                                                                                 ; (i = i1) → transportRefl (λ j → ∣ rCancel (merid north) k j ∣) k})
                                                                        (transp (λ j → isoToPath (Iso2-Kn-ΩKn+1 (suc n)) (i ∧ j)) (~ i)  ∣ north ∣))))

rUnitₖ' : (n : ℕ) (x : coHomK n) → x +[ n ]ₖ (0ₖ n) ≡ x
rUnitₖ' n x = commₖ n x (0ₖ n) ∙ lUnitₖ n x

-distrₖ : (n : ℕ) (x y : coHomK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ n x y = ((λ i → ΩKn+1→Kn (sym (Kn→ΩKn+1 n (ΩKn+1→Kn (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y))))) ∙∙
                      (λ i → ΩKn+1→Kn (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) i))) ∙∙
                      (λ i → ΩKn+1→Kn (symDistr (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) i))) ∙∙
                      (λ i → ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n y)) (~ i) ∙ (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Kn→ΩKn+1 n x)) (~ i)))) ∙∙
                      commₖ n (-[ n ]ₖ y) (-[ n ]ₖ x)

---- Group structure of cohomology groups ---

_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ {n = n} = sElim2 (λ _ _ → §) λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom n A → coHom n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

+ₕ-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom n A → coHom n A
-ₕ-syntax n = -ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x

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


-- Proof that rUnitₖ and lUnitₖ agree on 0ₖ. Needed for Mayer-Vietoris.
rUnitlUnit0 : (n : ℕ) → rUnitₖ n (0ₖ n) ≡ lUnitₖ n (0ₖ n)
rUnitlUnit0 0 = refl
rUnitlUnit0 (suc n) =
  (assoc (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) (0ₖ (suc n)) ∙ Kn→ΩKn+10ₖ (suc n) i))
         (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n))))))
         (Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))))
 ∙∙ (λ j → helper j
         ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (0ₖ (suc n)))
 ∙∙ sym (assoc (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) (0ₖ (suc n))))
               (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n))))))
               (Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (0ₖ (suc n))))

  where
  helper : (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) (0ₖ (suc n)) ∙ Kn→ΩKn+10ₖ (suc n) i))
          ∙ (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n))))))
          ≡ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) (0ₖ (suc n))))
          ∙ (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n))))))
  helper = ((λ j → lUnit (rUnit ((λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) (0ₖ (suc n)) ∙ Kn→ΩKn+10ₖ (suc n) i))) j) j
                   ∙ rUnit (cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n)))))) j)
         ∙∙ (λ j → ((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣ ∙ (λ i → ∣ rCancel (merid north) (z ∧ j) i ∣)))
                 ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) (0ₖ (suc n)) ∙ Kn→ΩKn+10ₖ (suc n) (i ∨ j)))
                 ∙ λ z → ΩKn+1→Kn (((λ i → ∣ rCancel (merid north) (z ∧ j) i ∣)) ∙ refl))
                 ∙ cong ΩKn+1→Kn (sym (rUnit (Kn→ΩKn+10ₖ (suc n) j)))
                 ∙ λ z → ΩKn+1→Kn (λ i → ∣ rCancel (merid north) ((~ z) ∧ j) i ∣))
         ∙∙ (λ j → (((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣ ∙ (λ i → ∣ rCancel (merid north) z i ∣))))
                  ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) (0ₖ (suc n)) ∙ refl))
                  ∙ λ z → ΩKn+1→Kn ((λ i → ∣ rCancel (merid north) z i ∣) ∙ λ i → ∣ rCancel (merid north) ((~ z) ∨ (~ j)) i ∣))
                 ∙ cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+10ₖ (suc n) (~ j))))
                 ∙ λ z → ΩKn+1→Kn (λ i → ∣ rCancel (merid north) (~ z ∧ (~ j)) i ∣)))
         ∙∙ (λ j → ((λ z → ΩKn+1→Kn (Kn→ΩKn+1 (suc n) ∣ north ∣  ∙ λ i → ∣ rCancel (merid north) (z ∧ (~ j)) i ∣))
                  ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (i ∧ j) ∙ Kn→ΩKn+10ₖ (suc n) (~ j)))
                  ∙ λ z → ΩKn+1→Kn ((λ i → ∣ rCancel (merid north) (z ∨ j) i ∣) ∙ λ i → ∣ rCancel (merid north) (~ z ∧ ~ j) i ∣))
                 ∙ rUnit (cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n)))))) (~ j))
         ∙∙ (λ j → lUnit (rUnit (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) i ∙ Kn→ΩKn+1 (suc n) (0ₖ (suc n)))) (~ j)) (~ j)
                 ∙ cong ΩKn+1→Kn (sym (lUnit (Kn→ΩKn+1 (suc n) (0ₖ (suc n))))))

---- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x) , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
+ₕ∙ (suc n) = sElim2 (λ _ _ → §) λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (suc n) ]ₖ b x) , (λ i → pa i +[ (suc n) ]ₖ pb i) ∙ lUnitₖ (suc n) (0ₖ (suc n)) ∣₂ }

-ₕ∙  : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A
-ₕ∙ zero = sRec § λ {(a , pt) → ∣ (λ x → -[ zero ]ₖ a x ) , (λ i → -[ zero ]ₖ (pt i)) ∣₂}
-ₕ∙ (suc n) = sRec § λ {(a , pt) → ∣ (λ x → -[ (suc n) ]ₖ a x ) , (λ i → -[ (suc n) ]ₖ (pt i)) ∙
                                                              (λ i → ΩKn+1→Kn (sym (Kn→ΩKn+10ₖ (suc n) i))) ∙
                                                              (λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ (suc n) (~ i))) ∙
                                                              Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) ∣ north ∣ ∣₂}

0ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A
0ₕ∙ zero = ∣ (λ _ → (0ₖ 0)) , refl ∣₂
0ₕ∙ (suc n) = ∣ (λ _ → (0ₖ (suc n))) , refl ∣₂

open IsSemigroup
open IsMonoid
open Group
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

--- ΩKₙ is commutative
isCommΩK : (n : ℕ) → (p q : typ (Ω (coHomK n , coHom-pt n))) → p ∙ q ≡ q ∙ p
isCommΩK zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK (suc n) p q =
  cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) p))
             (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) q))
  ∙∙ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n (ΩKn+1→Kn p) ∙ Kn→ΩKn+1 n (ΩKn+1→Kn q)))
  ∙∙ cong (Kn→ΩKn+1 n) (commₖ n (ΩKn+1→Kn p) (ΩKn+1→Kn q))
  ∙∙ Iso.rightInv (Iso3-Kn-ΩKn+1 n) (Kn→ΩKn+1 n (ΩKn+1→Kn q) ∙ Kn→ΩKn+1 n (ΩKn+1→Kn p)))
  ∙∙ sym (cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) q))
                   (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) p)))

--- the loopspace of Kₙ is commutative regardless of base
isCommΩK-based : (n : ℕ) (x : coHomK n) (p q : x ≡ x) → p ∙ q ≡ q ∙ p
isCommΩK-based zero x p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc n) x p q =
      sym (transport⁻Transport (typId x) (p ∙ q))
  ∙∙ (cong (transport (λ i → typId x (~ i))) (transpTypId p q)
  ∙∙  (λ i → transport (λ i → typId x (~ i)) (isCommΩK (suc n) (transport (λ i → typId x i) p) (transport (λ i → typId x i) q) i))
  ∙∙  cong (transport (λ i → typId x (~ i))) (sym (transpTypId q p)))
  ∙∙  transport⁻Transport (typId x) (q ∙ p)
  where
  congIsoHelper : (x : coHomK (suc n)) → Iso (coHomK (suc n)) (coHomK (suc n))
  Iso.fun (congIsoHelper x) = λ y → y +[ (suc n) ]ₖ x
  Iso.inv (congIsoHelper x) = λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)
  Iso.rightInv (congIsoHelper x) a = assocₖ (suc n) a (-[ (suc n) ]ₖ x) x ∙∙ cong (λ x → a +[ _ ]ₖ x) (lCancelₖ (suc n) x) ∙∙ rUnitₖ (suc n) a
  Iso.leftInv (congIsoHelper x) a = assocₖ (suc n) a x (-[ (suc n) ]ₖ x) ∙∙ cong (λ x → a +[ (suc n) ]ₖ x) (rCancelₖ (suc n) x) ∙∙ rUnitₖ (suc n) a

  typId : (x : coHomK (suc n)) → (x ≡ x) ≡ Path (coHomK (suc n)) (0ₖ _) (0ₖ _)
  typId x = isoToPath (congIso (invIso (congIsoHelper x))) ∙ λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i

  transpTypId : (p q : (x ≡ x)) → transport (λ i → typId x i) (p ∙ q) ≡ transport (λ i → typId x i) p ∙ transport (λ i → typId x i) q
  transpTypId p q =
      ((substComposite (λ x → x) (isoToPath ((congIso (invIso (congIsoHelper x)))))
                                 (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) (p ∙ q))
    ∙∙ (λ i → transport (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) (transportRefl (congFunct (λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)) p q i) i))
    ∙∙ overPathFunct (cong (λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)) p) (cong (λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)) q) (rCancelₖ (suc n) x))
    ∙∙ cong₂ (λ y z → transport (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) y ∙ transport (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) z)
             (sym (transportRefl (cong (λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)) p)))
             (sym (transportRefl (cong (λ y → y +[ (suc n) ]ₖ (-[ (suc n) ]ₖ x)) q)))
    ∙∙ cong₂ (_∙_) (sym (substComposite (λ x → x) (isoToPath ((congIso (invIso (congIsoHelper x))))) (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) p))
                   (sym (substComposite (λ x → x) (isoToPath ((congIso (invIso (congIsoHelper x))))) (λ i → rCancelₖ (suc n) x i ≡ rCancelₖ (suc n) x i) q))


addLemma : (a b : Int) → a +[ 0 ]ₖ b ≡ (a ℤ+ b)
addLemma a b = (cong ΩKn+1→Kn (sym (congFunct ∣_∣ (looper a) (looper b)))
              ∙∙ cong₂ (λ x y → ΩKn+1→Kn (λ i → ∣ (x ∙ y) i ∣)) (looper≡looper2 a) (looper≡looper2 b)
              ∙∙ (λ i → ΩKn+1→Kn (λ i → ∣ (cong SuspBool→S1 (cong S¹→SuspBool (intLoop a)) ∙ cong SuspBool→S1 (cong S¹→SuspBool (intLoop b))) i ∣ )))
              ∙∙ (cong (λ x → ΩKn+1→Kn (λ i → ∣ x i ∣)) (sym (congFunct SuspBool→S1 (cong S¹→SuspBool (intLoop a)) (cong S¹→SuspBool (intLoop b))))
              ∙∙ cong (λ x → ΩKn+1→Kn (cong ∣_∣ (cong SuspBool→S1 x))) (sym (congFunct S¹→SuspBool (intLoop a) (intLoop b)))
              ∙∙ cong (λ x → ΩKn+1→Kn (cong ∣_∣ (cong SuspBool→S1 (cong S¹→SuspBool x)))) (intLoop-hom a b))
              ∙∙ (cong (λ x → ΩKn+1→Kn (λ i → ∣ x i ∣)) (sym (looper≡looper2 (a ℤ+ b)))
                ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 zero) (a ℤ+ b))
