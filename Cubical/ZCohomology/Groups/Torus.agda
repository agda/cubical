{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso
                                           ; invIso to invGrIso ; idIso to idGrIso)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)

{- Proof that S¹→K2 is isomorphic to K2×K1 (as types). Needed for H²(T²)  -}
S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
Iso.fun S1→K2≡K2×K1 f = f north , ΩKn+1→Kn (sym (rCancelₖ (f north))
                                           ∙ (λ i → f (merid south i) +ₖ (-ₖ f (merid north i)))
                                           ∙ rCancelₖ (f south))
Iso.inv S1→K2≡K2×K1 (a , b) north = a +ₖ 0ₖ
Iso.inv S1→K2≡K2×K1 (a , b) south = a +ₖ 0ₖ
Iso.inv S1→K2≡K2×K1 (a , b) (merid south i) = a +ₖ (Kn→ΩKn+1 1 b i)
Iso.inv S1→K2≡K2×K1 (a , b) (merid north i) = a +ₖ 0ₖ
Iso.rightInv S1→K2≡K2×K1 (a , b) =
  ×≡ (rUnitₖ a)
     ((cong ΩKn+1→Kn (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +ₖ x) +ₖ (-ₖ (a +ₖ 0ₖ))) (funExt (λ x → sym (cancelHelper a x))) (rCancelₖ (a +ₖ 0ₖ))))
    ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 1) b)
    module _ where
    cancelHelper : (a b : hLevelTrunc 4 (S₊ 2)) → (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡ b
    cancelHelper a b =
      (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ))      ≡⟨ (λ i → (a +ₖ b) +ₖ (-ₖ (rUnitₖ a i))) ⟩≡⟨ cong (λ x → x +ₖ (-ₖ a)) (commₖ a b) ⟩
      (b +ₖ a) +ₖ (-ₖ a)             ≡⟨ assocₖ b a (-ₖ a) ⟩≡⟨ cong (λ x → b +ₖ x) (rCancelₖ a) ⟩
      (b +ₖ 0ₖ                       ≡⟨ rUnitₖ b ⟩
      b ∎)

    moveabout : {x : hLevelTrunc 4 (S₊ 2)} (p q : x ≡ 0ₖ) (mid : 0ₖ ≡ 0ₖ)
              → sym q ∙ (p ∙ mid ∙ sym p) ∙ q ≡ mid
    moveabout p q mid = (assoc (sym q) _ _
                      ∙∙ cong (_∙ q) (assoc (sym q) p (mid ∙ sym p))
                      ∙∙ sym (assoc (sym q ∙ p) (mid ∙ sym p) q))
                      ∙∙ (cong ((sym q ∙ p) ∙_) (sym (assoc mid (sym p) q))
                      ∙∙ cong (λ x → (sym q ∙ p) ∙ (mid ∙ x)) (sym (symDistr (sym q) p))
                      ∙∙ cong ((sym q ∙ p)∙_) (isCommΩK 2 mid _))
                      ∙∙ (assoc _ _ _
                      ∙∙ cong (_∙ mid) (rCancel (sym q ∙ p))
                      ∙∙ sym (lUnit mid))

    congHelper : ∀ {ℓ} {A : Type ℓ} {a1 : A} (p : a1 ≡ a1) (f : A → A) (id : (λ x → x) ≡ f)
               → cong f p ≡ sym (funExt⁻ id a1) ∙ p ∙ funExt⁻ id a1
    congHelper {a1 = a1}  p f id =
        (λ i → lUnit (rUnit (cong f p) i) i)
      ∙ (λ i → (λ j → id ((~ i) ∨ (~ j)) a1) ∙ cong (id (~ i)) p ∙ λ j → id (~ i ∨ j) a1)


    congHelper2 : (p : 0ₖ ≡ 0ₖ) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f)
                → (q : (f 0ₖ) ≡ 0ₖ)
                → (sym q) ∙ cong f p ∙ q ≡ p
    congHelper2 p f id q =
      cong (λ x → sym q ∙ x ∙ q) (congHelper p f id) ∙
      moveabout (sym (funExt⁻ id ∣ north ∣)) q p

Iso.leftInv S1→K2≡K2×K1 a =
  funExt λ {north → rUnitₖ (a north)
          ; south → rUnitₖ (a north) ∙ cong a (merid north)
          ; (merid south i) → m-south i
          ; (merid north i) → m-north i}
  where

  m-north : PathP (λ i → a north +ₖ ∣ north ∣ ≡ a (merid north i))
                (rUnitₖ (a north)) (rUnitₖ (a north) ∙ cong a (merid north))
  m-north i j =
    hcomp (λ k → λ { (i = i0) → rUnitₖ (a north) j
                    ; (j = i1) → a (merid north (i ∧ k))
                    ; (j = i0) → a north +ₖ ∣ north ∣})
          (rUnitₖ (a north) j)

  m-south : PathP (λ i → a north +ₖ Kn→ΩKn+1 1 (ΩKn+1→Kn (sym (rCancelₖ (a north))
                         ∙ (λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))
                         ∙ rCancelₖ (a south))) i ≡ a (merid south i)) (rUnitₖ (a north)) (rUnitₖ (a north) ∙ cong a (merid north))
  m-south j i =
    hcomp (λ k → λ { (i = i0) → (helper ∙∙ together ∙∙ congFunct (_+ₖ 0ₖ) (cong a (merid south)) (cong a (sym (merid north)))) (~ k) j
                    ; (i = i1) → a (merid south j)
                    ; (j = i0) → rUnitₖ (a north) i
                    ; (j = i1) → ((λ j → rUnitₖ (a (merid north ((~ k) ∧ j))) (j ∧ k)) ∙ λ j → rUnitₖ (a (merid north ((~ k) ∨ j))) (k ∨ j)) i })
          (hcomp (λ k → λ { (i = i1) → a (merid south j)
                           ; (i = i0) → compPath-filler ((cong (λ x → a x +ₖ 0ₖ) (merid south))) (cong (λ x → a x +ₖ 0ₖ) (sym (merid north))) k j
                           ; (j = i0) → rUnitₖ (a north) i
                           ; (j = i1) → pathFiller2 (cong (_+ₖ 0ₖ) (cong a (merid north))) (rUnitₖ (a south)) k i})
                  (rUnitₖ (a (merid south j)) i))


    where
    pathFiller : (rUnitₖ (a north) ∙ cong a (merid north)) ≡ cong (_+ₖ 0ₖ) (cong a (merid north)) ∙ rUnitₖ (a south)
    pathFiller = (λ i → (λ j → rUnitₖ (a (merid north (i ∧ j))) (j ∧ (~ i)))
               ∙ λ j → rUnitₖ (a (merid north (i ∨ j))) (~ i ∨ j))

    pathFiller2 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
    pathFiller2 p q i =
      hcomp (λ k → λ {(i = i0) → lUnit q (~ k)
                     ; (i = i1) → p ∙ q})
            ((λ j → p (~ i ∨ j)) ∙ q)

    helper : Path (_ ≡ _) (λ i → a north +ₖ Kn→ΩKn+1 1 (ΩKn+1→Kn (sym (rCancelₖ (a north))
                         ∙ (λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))
                         ∙ rCancelₖ (a south))) i)
                          ---
                          (cong (a north +ₖ_) (sym (rCancelₖ (a north)))
                         ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north)))
                           ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                         ∙ cong (a north +ₖ_) (rCancelₖ (a north)))
    helper =
        ((λ j i → a north +ₖ Iso.rightInv (Iso3-Kn-ΩKn+1 1) ((sym (rCancelₖ (a north))
                         ∙ (λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))
                         ∙ rCancelₖ (a south))) j i)
     ∙∙ congFunct (a north +ₖ_) (sym (rCancelₖ (a north))) ((λ i → a (merid south i) +ₖ (-ₖ a (merid north i))) ∙ rCancelₖ (a south))
     ∙∙ (λ j → cong (a north +ₖ_) (sym (rCancelₖ (a north)))
              ∙ congFunct (a north +ₖ_) ((λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))) (rCancelₖ (a south)) j))
     ∙∙ (λ j → cong (a north +ₖ_) (sym (rCancelₖ (a north)))
              ∙ cong₂Funct (λ x y → a north +ₖ a x +ₖ (-ₖ (a y))) (merid south) (merid north) j ∙ cong (a north +ₖ_) ((rCancelₖ (a south))))
     ∙∙ (λ i → cong (a north +ₖ_) (sym (rCancelₖ (a north)))
               ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north)))
               ∙ λ j → a north +ₖ a (merid north (~ i ∨ (~ j))) +ₖ (-ₖ (a (merid north (j ∧ (~ i))))))
               ∙ cong (a north +ₖ_) ((rCancelₖ (a (merid north (~ i))))))
    abstract
      pathHelper : (a b : hLevelTrunc 4 (S₊ 2)) → a +ₖ b +ₖ (-ₖ a) ≡ b +ₖ 0ₖ
      pathHelper a b =
          a +ₖ b +ₖ (-ₖ a)     ≡⟨ commₖ a (b +ₖ (-ₖ a)) ⟩≡⟨ assocₖ b (-ₖ a) a ⟩
          (b +ₖ (-ₖ a) +ₖ a     ≡⟨ cong (b +ₖ_) (lCancelₖ a) ⟩
           b +ₖ 0ₖ ∎)

    helperFun : ∀ {ℓ} {A : Type ℓ} {a b : A} (p p' : a ≡ b) (q q' : b ≡ b) (r : a ≡ a)
             → ((p q : a ≡ a) → p ∙ q ≡ q ∙ p)
             → q ≡ q'
             → PathP (λ i → p' (~ i) ≡ p' (~ i)) q' r
             → p ∙ q ∙ sym p ≡ r
    helperFun p p' q q' r comm qid dep =
      p ∙ q ∙ sym p                           ≡⟨ cong (λ x → p ∙ x ∙ sym p) qid
                                              ⟩≡⟨ cong (λ x → p ∙ x ∙ sym p) (λ i → lUnit (rUnit q' i) i) ⟩
      p ∙ (refl ∙ q' ∙ refl) ∙ sym p          ≡⟨ cong (λ x → p ∙ x ∙ sym p) (λ i → (λ j → p' (~ i ∨ ~ j)) ∙ dep i ∙ λ j → p' (~ i ∨ j))
                                              ⟩≡⟨ assoc p (sym p' ∙ r ∙ p') (sym p) ⟩
      (p ∙ sym p' ∙ r ∙ p') ∙ sym p           ≡⟨ cong (_∙ sym p) (assoc p (sym p') (r ∙ p'))
                                              ⟩≡⟨ sym (assoc (p ∙ sym p') (r ∙ p') (sym p)) ⟩
      (p ∙ sym p') ∙ (r ∙ p') ∙ sym p         ≡⟨ cong ((p ∙ sym p') ∙_) (sym (assoc r p' (sym p)))
                                              ⟩≡⟨ cong (λ x → (p ∙ sym p') ∙ r ∙ x) (sym (symDistr p (sym p'))) ⟩
      (p ∙ sym p') ∙ r ∙ sym (p ∙ sym p')     ≡⟨ cong ((p ∙ sym p') ∙_) (comm r (sym (p ∙ sym p')))
                                              ⟩≡⟨ assoc (p ∙ sym p') (sym (p ∙ sym p')) r ⟩
      ((p ∙ sym p') ∙ sym (p ∙ sym p')) ∙ r   ≡⟨ cong (_∙ r) (rCancel (p ∙ sym p')) ⟩≡⟨ sym (lUnit r) ⟩
      r ∎

    together : Path (_ ≡ _) (cong (a north +ₖ_) (sym (rCancelₖ (a north)))
                           ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                           ∙ cong (a north +ₖ_) (rCancelₖ (a north)))
                            (cong(_+ₖ 0ₖ) (cong a (merid south) ∙ cong a (sym (merid north))))
    together =
      helperFun (cong (a north +ₖ_) (sym (rCancelₖ (a north))))
                (λ i → pathHelper (a north) (a north) (~ i))
                ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                (((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north))))
                (cong(_+ₖ 0ₖ) (cong a (merid south) ∙ cong a (sym (merid north))))
                (isCommΩK-based 2 _)
                refl
                λ i → hcomp (λ k → λ {(i = i0) → (λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north)))
                                                  ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north))
                                      ; (i = i1) → congFunct (_+ₖ 0ₖ) (cong a (merid south)) (cong a (sym (merid north))) (~ k)})
                             ((λ j → pathHelper (a north) (a (merid south j)) i) ∙ (λ j → pathHelper (a north) (a (merid north (~ j))) i))



--------- H⁰(T²) ------------
H⁰-T²≅0 : grIso (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
H⁰-T²≅0 =
  Iso'→Iso
    (iso'
      (iso (sRec isSetInt (λ f → f (north , north)))
           (λ a → ∣ (λ x → a) ∣₂)
           (λ a → refl)
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → cong ∣_∣₂
                      (funExt λ {(x , y) → suspToPropRec2
                                              {B = λ x y → f (north , north) ≡ f (x , y)}
                                              north
                                              (λ _ _ → isSetInt _ _)
                                              refl
                                              x y})))
      (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
              λ a b → addLemma (a (north , north)) (b (north , north))))



------------------ H¹(T²) -------------------------------

-- We first need the following technical lemma
basechange-lemma2 : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹)
                 → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                  ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                  ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
basechange-lemma2 f g F = coInd f g F (f base) (g base) refl refl
  where
  coInd : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹) (x y : hLevelTrunc 3 (S₊ 1))
                   → f base ≡ x
                   → g base ≡ y
                   → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                    ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                    ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
  coInd f g F =
    elim2 (λ _ _ → isGroupoidΠ2 λ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isGroupoidS¹ base base)) _ _ )
          (suspToPropRec2
            north
            (λ _ _ → isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _)
            λ fid gid →
                ((λ i → basechange2⁻ (F (f base +ₖ g base)) (cong₂Funct (λ x y → F (f x +ₖ g y)) loop loop i))
              ∙ (basechange2⁻-morph (F (f base +ₖ g base))
                                    (cong (λ x → F (f x +ₖ g base)) loop)
                                    (cong (λ x → F (f base +ₖ g x)) loop)))
              ∙∙ (λ i → basechange2⁻ (F (f base +ₖ gid i)) (cong (λ x → F (f x +ₖ gid i)) loop)
                      ∙ basechange2⁻ (F (fid i +ₖ g base)) (cong (λ x → F (fid i +ₖ g x)) loop))
              ∙∙ (λ i → basechange2⁻ (F (rUnitₖ (f base) i)) (cong (λ x → F (rUnitₖ (f x) i)) loop)
                      ∙ basechange2⁻ (F (lUnitₖ (g base) i)) (cong (λ x → F (lUnitₖ (g x) i)) loop)))


S1→K₁≡S1×Int : Iso ((S₊ 1) → hLevelTrunc 3 (S₊ 1)) ((hLevelTrunc 3 (S₊ 1)) × Int)
S1→K₁≡S1×Int = compIso helper2 (compIso S¹→S¹≡S¹×Int helper)
  where
  helper : Iso (S¹ × Int) (hLevelTrunc 3 (S₊ 1) × Int)
  Iso.fun helper (s , int) = ∣ S¹→S1 s  ∣ , int
  Iso.inv helper (s , int) = (S1→S¹ (S1map s)) , int
  Iso.rightInv helper (s , int) =
    trElim {B = λ s → (∣ S¹→S1 (S1→S¹ (S1map s)) ∣ , int) ≡ (s , int)}
           (λ _ → isOfHLevelPath 3 (isOfHLevelProd 3 (isOfHLevelTrunc 3) (isOfHLevelSuc 2 isSetInt)) _ _)
           (λ a → ×≡ (cong ∣_∣ (S1→S¹-retr a)) refl)
           s
  Iso.leftInv helper (s , int) = ×≡ (S1→S¹-sect s) refl

  helper2 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
  Iso.fun helper2 f x = trMap S1→S¹ (f (S¹→S1 x))
  Iso.inv helper2 f x = trMap S¹→S1 (f (S1→S¹ x))
  Iso.rightInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-sect x i)) i
    where
    helper3 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
    helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                     λ a → cong ∣_∣ (S1→S¹-sect a)
  Iso.leftInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-retr x i)) i
    where
    helper3 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
    helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                     λ a → cong ∣_∣ (S1→S¹-retr a)


H¹-T²≅ℤ×ℤ : grIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
H¹-T²≅ℤ×ℤ =
  compGrIso
    (Iso'→Iso
      (iso' (compIso
                (setTruncIso (compIso
                               curryIso
                               (compIso
                                 (codomainIso S1→K₁≡S1×Int)
                                 toProdIso)))
                (setTruncOfProdIso))
                (sElim2
                    (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                    λ f g → ×≡ (cong ∣_∣₂
                                     (funExt (λ x → helper (f (x , S¹→S1 base) +ₖ g (x , S¹→S1 base))
                                                   ∙ sym (cong₂ (λ x y → x +ₖ y)
                                                                (helper (f (x , S¹→S1 base)))
                                                                (helper (g (x , S¹→S1 base)))))))
                                (cong ∣_∣₂
                                   (funExt
                                     (suspToPropRec
                                        north
                                        (λ _ → isSetInt _ _)
                                        (cong winding
                                              (basechange-lemma2
                                                (λ x → f (north , S¹→S1 x))
                                                (λ x → g (north , S¹→S1 x))
                                                λ x → S¹map (trMap S1→S¹ x))
                                       ∙∙ winding-hom
                                           (basechange2⁻
                                               (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                               (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i))))))
                                           (basechange2⁻
                                               (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                               (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i))))))
                                       ∙∙ sym (addLemma
                                               (winding
                                                 (basechange2⁻
                                                   (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                                   (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i)))))))
                                               (winding
                                                 (basechange2⁻
                                                   (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                                   (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i)))))))))))))))
    (dirProdIso (invGrIso (Hⁿ-Sⁿ≅ℤ 0)) (invGrIso H⁰-S¹≅ℤ))

  where
  helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ S¹→S1 (S¹map (trMap S1→S¹ x)) ∣ ≡ x
  helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-retr a)

-------------------------------------------------------------


----------------------- H²(T²) ------------------------------

H²-T²≡ℤ : Iso Int (coHom 2 (S₊ 1 × S₊ 1))
H²-T²≡ℤ =
    compIso
          helper'
          (compIso
            (symIso (prodIso (groupIso→Iso H²-S¹≅0)
                             (groupIso→Iso (invGrIso (Hⁿ-Sⁿ≅ℤ 0)))))
            (compIso
              (symIso setTruncOfProdIso)
              (symIso
                (setTruncIso
                  (compIso
                    curryIso
                    (compIso
                      (codomainIso S1→K2≡K2×K1)
                      toProdIso))))))
  where
  helper' : Iso Int (Unit × Int)
  Iso.inv helper' = proj₂
  Iso.fun helper' x = tt , x
  Iso.leftInv helper' x = refl
  Iso.rightInv helper' x = ×≡ refl refl

-- Showing that the map from ℤ to H²(T²) is a morphism should be easy, but it gets somewhat messy.
-- Posponing it for now.
