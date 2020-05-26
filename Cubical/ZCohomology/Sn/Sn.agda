{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Sn.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.S1.S1
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisReduced
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
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso)


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)

pushoutSn : (n : ℕ) → Iso (S₊ (suc n)) (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
Iso.fun (pushoutSn n) north = inl tt
Iso.fun (pushoutSn n) south = inr tt
Iso.fun (pushoutSn n) (merid a i) = push a i
Iso.inv (pushoutSn n) (inl x) = north
Iso.inv (pushoutSn n) (inr x) = south
Iso.inv (pushoutSn n) (push a i) = merid a i
Iso.rightInv (pushoutSn n) (inl x) = refl
Iso.rightInv (pushoutSn n) (inr x) = refl
Iso.rightInv (pushoutSn n) (push a i) = refl
Iso.leftInv (pushoutSn n) north = refl
Iso.leftInv (pushoutSn n) south = refl
Iso.leftInv (pushoutSn n) (merid a i) = refl

Sn≡Pushout : (n : ℕ) → (S₊ (suc n)) ≡ (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt)
Sn≡Pushout n = isoToPath (pushoutSn n)

isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
isContr→≡Unit contr = isoToPath (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)

isContr→isContrTrunc : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr (hLevelTrunc n A)
isContr→isContrTrunc n contr = ∣ fst contr ∣ , (trElim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (snd contr a))
isContr→isContrSetTrunc : ∀ {ℓ} {A : Type ℓ} → isContr A → isContr (∥ A ∥₀)
isContr→isContrSetTrunc contr = ∣ fst contr ∣₀ , sElim (λ _ → isOfHLevelPath 2 (setTruncIsSet) _ _) λ a → cong ∣_∣₀ (snd contr a)

-- coHom Unit


lemma10000 : (n : ℕ) → looper (pos (suc n)) ≡ loop* ∙ looper (pos n)
lemma10000 zero = sym (lUnit loop*) ∙ rUnit loop*
lemma10000 (suc n) = (λ i → (lemma10000 n i) ∙ loop*) ∙ sym (assoc loop* (looper (pos n)) loop*)

lemma10001 : (a : Int) → looper (sucInt a) ≡ loop* ∙ looper a
lemma10001 (pos n) = lemma10000 n
lemma10001 (negsuc zero) = sym (rCancel loop*)
lemma10001 (negsuc (suc zero)) = lUnit (sym loop*)
                               ∙ (λ i → rCancel loop* (~ i) ∙ (sym loop*))
                               ∙ sym (assoc loop* (sym loop*) (sym loop*))
lemma10001 (negsuc (suc (suc n))) = cong (λ x → x ∙ (sym loop*)) (lemma10001 (negsuc (suc n)))
                                  ∙ sym (assoc loop* (looper (negsuc n) ∙ sym loop*) (sym loop*))

lemma10002 : (a : Int) → looper (predInt a) ≡ sym loop* ∙ looper a
lemma10002 (pos zero) = rUnit (sym loop*)
lemma10002 (pos (suc n)) = lUnit (looper (pos n))
                         ∙ (λ i → lCancel loop* (~ i) ∙ (looper (pos n)))
                         ∙ sym (assoc (sym loop*) loop* (looper (pos n)))
                         ∙ λ i → sym loop* ∙ lemma10000 n (~ i)
lemma10002 (negsuc zero) = refl
lemma10002 (negsuc (suc n)) = (λ i → (lemma10002 (negsuc n) i) ∙ sym loop*) ∙ sym (assoc (sym loop*) (looper (negsuc n)) (sym loop*))

-- loop*comm : (a : Int) → looper a ∙ loop* ≡ loop* ∙ looper a
-- loop*comm (pos zero) = sym (lUnit loop*) ∙ rUnit loop*
-- loop*comm (pos (suc n)) = (λ i → loop*comm (pos n) i ∙ loop*) ∙ sym (assoc loop* (looper (pos n)) loop*)
-- loop*comm (negsuc zero) = lCancel loop* ∙ sym (rCancel loop*)
-- loop*comm (negsuc (suc n)) = sym (assoc (looper (negsuc n)) (sym loop*) loop*)
--                            ∙ (λ i → looper (negsuc n) ∙ lCancel loop* i)
--                            ∙ (λ i → looper (negsuc n) ∙ rCancel loop* (~ i))
--                            ∙ assoc (looper (negsuc n)) loop* (sym loop*)
--                            ∙ (λ i → loop*comm (negsuc n) i ∙ sym loop*)
--                            ∙ sym (assoc loop* (looper (negsuc n)) (sym loop*))
-- symloop*comm : (a : Int) → looper a ∙ sym loop* ≡ sym loop* ∙ looper a
-- symloop*comm (pos zero) = sym (lUnit (sym loop*)) ∙ rUnit (sym loop*)
-- symloop*comm (pos (suc n)) = sym (assoc (looper (pos n)) loop* (sym loop*))
--                            ∙ (λ i → looper (pos n) ∙ (rCancel loop* i))
--                            ∙ (λ i → looper (pos n) ∙ lCancel loop* (~ i))
--                            ∙ assoc (looper (pos n)) (sym loop*) loop*
--                            ∙ (λ i → symloop*comm (pos n) i ∙ loop*)
--                            ∙ sym (assoc (sym loop*) (looper (pos n)) loop*)
-- symloop*comm (negsuc zero) = refl 
-- symloop*comm (negsuc (suc n)) = (λ i → symloop*comm (negsuc n) i ∙ sym loop*)
--                               ∙ sym (assoc (sym loop*) (looper (negsuc n)) (sym loop*))


sucIntPredInt : (a : Int) → sucInt (predInt a) ≡ a
sucIntPredInt (pos zero) = refl
sucIntPredInt (pos (suc n)) = refl
sucIntPredInt (negsuc n) = refl

looperId : (a b : Int) → looper a ∙ looper b ≡ looper (a +ℤ b)
looperId (pos zero) b = sym (lUnit (looper b)) ∙ λ i → looper (pos0+ b i)
looperId (pos (suc n)) (pos zero) = sym (rUnit (looper (pos (suc n))))
looperId (pos (suc n)) (pos (suc m)) = (λ i → (lemma10000 n i) ∙ looper (pos (suc m)))
                                 ∙ sym (assoc loop* (looper (pos n)) (looper (pos (suc m))))
                                 ∙ (λ i → loop* ∙ looperId (pos n) (pos (suc m)) i)
                                 ∙ sym (lemma10001 (sucInt (pos n +pos m)))
                                 ∙ λ i → looper (sucInt (sucInt+pos m (pos n) i))
looperId (pos (suc n)) (negsuc zero) = sym (assoc (looper (pos n)) loop* (sym loop*)) ∙ (λ i → looper (pos n) ∙ (rCancel loop* i)) ∙ sym (rUnit (looper (pos n))) 
looperId (pos (suc n)) (negsuc (suc m)) = (λ i → (looper (pos n) ∙ loop*) ∙ lemma10002 (negsuc m) i)
                                        ∙ sym (assoc (looper (pos n)) loop* (sym loop* ∙ looper (negsuc m)))
                                        ∙ (λ i → looper (pos n) ∙ assoc loop* (sym loop*) (looper (negsuc m)) i)
                                        ∙ (λ i → looper (pos n) ∙ rCancel loop* i ∙ looper (negsuc m))
                                        ∙ (λ i → looper (pos n) ∙ lUnit (looper (negsuc m)) (~ i))
                                        ∙ looperId (pos n) (negsuc m)
                                        ∙ λ i → looper (predInt+negsuc m (pos (suc n)) (~ i))
looperId (negsuc zero) (pos zero) = sym (rUnit (sym loop*))
looperId (negsuc zero) (pos (suc n)) = (λ i → (sym loop*) ∙ lemma10001 (pos n) i)
                                     ∙ assoc (sym loop*) loop* (looper (pos n))
                                     ∙ (λ i → lCancel loop* i ∙ looper (pos n))
                                     ∙ sym (lUnit (looper (pos n)))
                                     ∙ (λ i → looper (sucIntPredInt (pos n) (~ i)))
                                     ∙ λ i → looper (sucInt (negsuc0+ (pos n) i))
looperId (negsuc zero) (negsuc zero) = refl
looperId (negsuc zero) (negsuc (suc n)) = assoc (sym loop*) (looper (negsuc n)) (sym loop*) ∙
                                          (λ i → looperId (negsuc zero) (negsuc n) i ∙ sym loop*) ∙
                                          (λ i → looper (negsuc zero +negsuc n) ∙ sym loop*) ∙
                                          (λ i → looper (negsuc0+ (negsuc n) (~ i)) ∙ sym loop*) ∙
                                          λ i → looper (predInt (negsuc0+ (negsuc n) i)) 
looperId (negsuc (suc n)) b = (λ i → lemma10002 (negsuc n) i ∙ looper b)
                            ∙ sym (assoc (sym loop*) (looper (negsuc n)) (looper b))
                            ∙ (λ i → sym loop* ∙ looperId (negsuc n) b i)
                            ∙ sym (lemma10002 (negsuc n +ℤ b)) 
                            ∙ λ i → looper (predInt+ (negsuc n) b i)

addLemma : (a b : Int) → a +ₖ b ≡ (a +ℤ b)
addLemma a b = (λ i → ΩKn+1→Kn (cong ∣_∣ (looper a) ∙ cong ∣_∣ (looper b)))
             ∙ (λ i → ΩKn+1→Kn (congFunct ∣_∣ (looper a) (looper b) (~ i)))
             ∙ (λ i → ΩKn+1→Kn (cong ∣_∣ (looperId a b i)))
             ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 zero) (a +ℤ b)


coHomGrUnit0 : grIso (coHomGr 0 Unit) intGroup
grIso.fun coHomGrUnit0 = sRec isSetInt (λ f → f tt) ,
                         sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a tt) (b tt)
grIso.inv coHomGrUnit0 = (λ a → ∣ (λ _ → a) ∣₀) , λ a b i → ∣ (λ _ → addLemma a b (~ i)) ∣₀
grIso.rightInv coHomGrUnit0 a = refl
grIso.leftInv coHomGrUnit0 = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl

coHomGrUnit≥1 : (n : ℕ) → grIso (coHomGr (suc n) Unit) trivialGroup
grIso.fun (coHomGrUnit≥1 n) = (λ _ → tt) , (λ _ _ → refl)
grIso.inv (coHomGrUnit≥1 n) = (λ _ → ∣ (λ _ → ∣ north ∣) ∣₀) , λ _ _ → sym (rUnitₕ 0ₕ)
grIso.rightInv (coHomGrUnit≥1 n) a = refl
grIso.leftInv (coHomGrUnit≥1 n) a = sym (helper2 .snd 0ₕ) ∙ helper2 .snd a
  where
  helper : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₀)
  helper n = subst isContr ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n))) ∙ sym propTrunc≡Trunc0 ∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₀)
                            (isConnectedSubtr 2 (helper2 n .fst) (subst (λ x → isHLevelConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
    where
    helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
    helper2 zero = 0 , refl
    helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)

  helper2 : isContr (coHom (suc n) Unit)
  helper2 = subst isContr (λ i → ∥ UnitToTypeId (coHomK (suc n)) (~ i) ∥₀) (helper n)

coHom0-S0 : grIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
coHom0-S0 =
  Iso'→Iso
    (iso'
      (iso (sRec (isOfHLevelProd 2 isSetInt isSetInt)
                 λ f → (f north) , (f south))
           (λ {(a , b) → ∣ (λ {north → a ; south → b}) ∣₀})
           (λ { (a , b) → refl})
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → cong ∣_∣₀ (funExt (λ {north → refl ; south → refl}))))
      (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 isSetInt isSetInt) _ _)
              λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i))

coHomGr0-S1 : grIso (coHomGr 1 (S₊ 1)) intGroup
coHomGr0-S1 =
  Iso'→Iso
    (iso'
      (iso (sRec isSetInt {!!})
           {!!}
           {!!}
           {!!})
      {!!})
