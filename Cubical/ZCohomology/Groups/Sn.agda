{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.S1.S1
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
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
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; rec to trRec2 ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.GroupLibrary
open import Cubical.ZCohomology.coHomZero-map
open import Cubical.HITs.Wedge

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.ZCohomology.Groups.Unit


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)


{- Proof that S¹→K2 is isomorphic to K2×K1 
Gives a better computing proof that Used for H¹(S²)≡0 which does not rely om Mayer Vietoris
Also needed for H²(T²)  -}
S1→K2≡K2×K1 : Iso (S₊ 1 → hLevelTrunc 4 (S₊ 2)) (hLevelTrunc 4 (S₊ 2) × hLevelTrunc 3 (S₊ 1))
Iso.fun S1→K2≡K2×K1 f = f north , ΩKn+1→Kn (sym (rCancelₖ (f north))
                                           ∙ (λ i → f (merid south i) +ₖ (-ₖ f (merid north i)))
                                           ∙ rCancelₖ (f south))
Iso.inv S1→K2≡K2×K1 (a , b) north = a +ₖ 0ₖ
Iso.inv S1→K2≡K2×K1 (a , b) south = a +ₖ 0ₖ
Iso.inv S1→K2≡K2×K1 (a , b) (merid south i) = a +ₖ (Kn→ΩKn+1 1 b i)
Iso.inv S1→K2≡K2×K1 (a , b) (merid north i) = a +ₖ 0ₖ
Iso.rightInv S1→K2≡K2×K1 (a , b) =
  ×≡ (rUnitₖ a)
     ((cong ΩKn+1→Kn (congHelper++ (Kn→ΩKn+1 1 b) (λ x → (a +ₖ x) +ₖ (-ₖ (a +ₖ 0ₖ))) (funExt (λ x → sym (cancelHelper a x))) (rCancelₖ (a +ₖ 0ₖ))))
    ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 1) b)
    module _ where
    cancelHelper : (a b : hLevelTrunc 4 (S₊ 2)) → (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡ b
    cancelHelper a b =
      (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡⟨ (λ i → (a +ₖ b) +ₖ (-ₖ (rUnitₖ a i))) ⟩
      (a +ₖ b) +ₖ (-ₖ a) ≡⟨ cong (λ x → x +ₖ (-ₖ a)) (commₖ a b) ⟩
      (b +ₖ a) +ₖ (-ₖ a) ≡⟨ assocₖ b a (-ₖ a) ⟩
      b +ₖ a +ₖ (-ₖ a) ≡⟨ cong (λ x → b +ₖ x) (rCancelₖ a) ⟩
      b +ₖ 0ₖ ≡⟨ rUnitₖ b ⟩
      b ∎

    abstract
      commHelper : (p q : Path (hLevelTrunc 4 (S₊ 2)) 0ₖ 0ₖ) → p ∙ q ≡ q ∙ p
      commHelper p q =
          cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) p))
                    (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) q))
        ∙ sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) (Kn→ΩKn+1 1 (ΩKn+1→Kn p) ∙ Kn→ΩKn+1 1 (ΩKn+1→Kn q)))
        ∙ cong (Kn→ΩKn+1 1) (commₖ (ΩKn+1→Kn p) (ΩKn+1→Kn q))
        ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 1) (Kn→ΩKn+1 1 (ΩKn+1→Kn q) ∙ Kn→ΩKn+1 1 (ΩKn+1→Kn p))
        ∙ sym (cong₂ _∙_ (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) q))
                         (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 1) p)))

    moveabout : {x : hLevelTrunc 4 (S₊ 2)} (p q : x ≡ 0ₖ) (mid : 0ₖ ≡ 0ₖ)
              → sym q ∙ (p ∙ mid ∙ sym p) ∙ q ≡ mid
    moveabout p q mid = assoc (sym q) _ _
                      ∙ cong (_∙ q) (assoc (sym q) p (mid ∙ sym p))
                      ∙ sym (assoc (sym q ∙ p) (mid ∙ sym p) q)
                      ∙ cong ((sym q ∙ p) ∙_) (sym (assoc mid (sym p) q))
                      ∙ cong (λ x → (sym q ∙ p) ∙ (mid ∙ x)) (sym (symDistr (sym q) p))
                      ∙ cong ((sym q ∙ p)∙_) (commHelper mid _)
                      ∙ assoc _ _ _
                      ∙ cong (_∙ mid) (rCancel (sym q ∙ p))
                      ∙ sym (lUnit mid)
    
    congHelper : ∀ {ℓ} {A : Type ℓ} {a1 : A} (p : a1 ≡ a1) (f : A → A) (id : (λ x → x) ≡ f) 
               → cong f p ≡ sym (funExt⁻ id a1) ∙ p ∙ funExt⁻ id a1
    congHelper {a1 = a1}  p f id =
        (λ i → lUnit (rUnit (cong f p) i) i)
      ∙ (λ i → (λ j → id ((~ i) ∨ (~ j)) a1) ∙ cong (id (~ i)) p ∙ λ j → id (~ i ∨ j) a1)


    congHelper++ : (p : 0ₖ ≡ 0ₖ) (f : hLevelTrunc 4 (S₊ 2) → hLevelTrunc 4 (S₊ 2)) (id : (λ x → x) ≡ f)
                → (q : (f 0ₖ) ≡ 0ₖ)
                → (sym q) ∙ cong f p ∙ q ≡ p
    congHelper++ p f id q =
      cong (λ x → sym q ∙ x ∙ q) (congHelper p f id) ∙
      moveabout (sym (funExt⁻ id ∣ north ∣)) q p
    
Iso.leftInv S1→K2≡K2×K1 a =
  funExt λ {north → rUnitₖ (a north)
          ; south → rUnitₖ (a north) ∙ cong a (merid north)
          ; (merid south i) → test i
          ; (merid north i) → test2 i}
  where
  test : PathP (λ i → a north +ₖ Kn→ΩKn+1 1 (ΩKn+1→Kn (sym (rCancelₖ (a north))
                         ∙ (λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))
                         ∙ rCancelₖ (a south))) i ≡ a (merid south i)) (rUnitₖ (a north)) (rUnitₖ (a north) ∙ cong a (merid north))
  test j i =
    hcomp (λ k → λ { (i = i0) → (helper ∙ together ∙ congFunct (_+ₖ 0ₖ) (cong a (merid south)) (cong a (sym (merid north)))) (~ k) j
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
    pathFiller = (λ i → (λ j → rUnitₖ (a (merid north (i ∧ j))) (j ∧ (~ i))) ∙ λ j → rUnitₖ (a (merid north (i ∨ j))) (~ i ∨ j))

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
                         ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                         ∙ cong (a north +ₖ_) (rCancelₖ (a north)))
    helper =
      (λ j i → a north +ₖ Iso.rightInv (Iso3-Kn-ΩKn+1 1) ((sym (rCancelₖ (a north))
                         ∙ (λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))
                         ∙ rCancelₖ (a south))) j i) ∙
      congFunct (a north +ₖ_) (sym (rCancelₖ (a north))) ((λ i → a (merid south i) +ₖ (-ₖ a (merid north i))) ∙ rCancelₖ (a south)) ∙
      (λ j → cong (a north +ₖ_) (sym (rCancelₖ (a north))) ∙ congFunct (a north +ₖ_) ((λ i → a (merid south i) +ₖ (-ₖ a (merid north i)))) (rCancelₖ (a south)) j) ∙
      (λ j → cong (a north +ₖ_) (sym (rCancelₖ (a north))) ∙ cong₂Funct (λ x y → a north +ₖ a x +ₖ (-ₖ (a y))) (merid south) (merid north) j ∙ cong (a north +ₖ_) ((rCancelₖ (a south)))) ∙
      (λ i → cong (a north +ₖ_) (sym (rCancelₖ (a north))) ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ i ∨ (~ j))) +ₖ (-ₖ (a (merid north (j ∧ (~ i)))))) ∙ cong (a north +ₖ_) ((rCancelₖ (a (merid north (~ i))))))

    abstract
      pathHelper : (a b : hLevelTrunc 4 (S₊ 2)) → a +ₖ b +ₖ (-ₖ a) ≡ b +ₖ 0ₖ
      pathHelper a b =
          a +ₖ b +ₖ (-ₖ a)     ≡⟨ commₖ a (b +ₖ (-ₖ a)) ⟩
          (b +ₖ (-ₖ a)) +ₖ a   ≡⟨ assocₖ b (-ₖ a) a ⟩
          b +ₖ (-ₖ a) +ₖ a     ≡⟨ cong (b +ₖ_) (lCancelₖ a) ⟩
          b +ₖ 0ₖ ∎


    helperFun : ∀ {ℓ} {A : Type ℓ} {a b : A} (p p' : a ≡ b) (q q' : b ≡ b) (r : a ≡ a) 
             → ((p q : a ≡ a) → p ∙ q ≡ q ∙ p)
             → q ≡ q'
             → PathP (λ i → p' (~ i) ≡ p' (~ i)) q' r
             → p ∙ q ∙ sym p ≡ r
    helperFun p p' q q' r comm qid dep =
      p ∙ q ∙ sym p                          ≡⟨ cong (λ x → p ∙ x ∙ sym p) qid ⟩
      p ∙ q' ∙ sym p                         ≡⟨ cong (λ x → p ∙ x ∙ sym p) (λ i → lUnit (rUnit q' i) i) ⟩
      p ∙ (refl ∙ q' ∙ refl) ∙ sym p         ≡⟨ cong (λ x → p ∙ x ∙ sym p) (λ i → (λ j → p' (~ i ∨ ~ j)) ∙ dep i ∙ λ j → p' (~ i ∨ j)) ⟩
      p ∙ (sym p' ∙ r ∙ p') ∙ sym p          ≡⟨ assoc p (sym p' ∙ r ∙ p') (sym p) ⟩
      (p ∙ sym p' ∙ r ∙ p') ∙ sym p          ≡⟨ cong (_∙ sym p) (assoc p (sym p') (r ∙ p')) ⟩
      ((p ∙ sym p') ∙ r ∙ p') ∙ sym p        ≡⟨ sym (assoc (p ∙ sym p') (r ∙ p') (sym p)) ⟩
      (p ∙ sym p') ∙ (r ∙ p') ∙ sym p        ≡⟨ cong ((p ∙ sym p') ∙_) (sym (assoc r p' (sym p))) ⟩
      (p ∙ sym p') ∙ r ∙ (p' ∙ sym p)        ≡⟨ cong (λ x → (p ∙ sym p') ∙ r ∙ x) (sym (symDistr p (sym p'))) ⟩
      (p ∙ sym p') ∙ r ∙ sym (p ∙ sym p')    ≡⟨ cong ((p ∙ sym p') ∙_) (comm r (sym (p ∙ sym p'))) ⟩
      (p ∙ sym p') ∙ sym (p ∙ sym p') ∙ r    ≡⟨ assoc (p ∙ sym p') (sym (p ∙ sym p')) r ⟩
      ((p ∙ sym p') ∙ sym (p ∙ sym p')) ∙ r  ≡⟨ cong (_∙ r) (rCancel (p ∙ sym p')) ⟩
      refl ∙ r ≡⟨ sym (lUnit r) ⟩
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
      (transport (λ i → (p q : rUnitₖ (a north) (~ i) ≡ rUnitₖ (a north) (~ i)) → p ∙ q ≡ q ∙ p)
        (λ p q → isCommS2 _ p q))
      refl
      λ i → hcomp (λ k → λ {(i = i0) → (λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north))
                           ; (i = i1) → congFunct (_+ₖ 0ₖ) (cong a (merid south)) (cong a (sym (merid north))) (~ k)})
                   ((λ j → pathHelper (a north) (a (merid south j)) i) ∙ (λ j → pathHelper (a north) (a (merid north (~ j))) i))
      where
      isCommS2 : (x : hLevelTrunc 4 (S₊ 2)) (p q : x ≡ x) → p ∙ q ≡ q ∙ p
      isCommS2 x p q = sym (transport⁻Transport (typId x) (p ∙ q))
                     ∙ cong (transport (λ i → typId x (~ i))) (typIdHelper p q)
                     ∙ (λ i → transport (λ i → typId x (~ i)) (commHelper ∣ north ∣ ∣ north ∣ (transport (λ i → typId x i) p) (transport (λ i → typId x i) q) i))
                     ∙ cong (transport (λ i → typId x (~ i))) (sym (typIdHelper q p))
                     ∙ transport⁻Transport (typId x) (q ∙ p)
        where
        congIsoHelper : (x : hLevelTrunc 4 (S₊ 2)) → Iso (hLevelTrunc 4 (S₊ 2)) (hLevelTrunc 4 (S₊ 2))
        Iso.fun (congIsoHelper x) = _+ₖ x
        Iso.inv (congIsoHelper x) = _+ₖ (-ₖ x)
        Iso.rightInv (congIsoHelper x) a = assocₖ a (-ₖ x) x ∙ cong (a +ₖ_) (lCancelₖ x) ∙ rUnitₖ a
        Iso.leftInv (congIsoHelper x) a = assocₖ a x (-ₖ x) ∙ cong (a +ₖ_) (rCancelₖ x) ∙ rUnitₖ a

        typId : (x : hLevelTrunc 4 (S₊ 2)) → (x ≡ x) ≡ Path (hLevelTrunc 4 (S₊ 2)) 0ₖ 0ₖ
        typId x = isoToPath ((congIso (isoToEquiv (symIso (congIsoHelper x))))) ∙ λ i → rCancelₖ x i ≡ rCancelₖ x i

        typIdHelper : (p q : (x ≡ x)) → transport (λ i → typId x i) (p ∙ q) ≡ transport (λ i → typId x i) p ∙ transport (λ i → typId x i) q
        typIdHelper p q =
            (substComposite (λ x → x) (isoToPath ((congIso (isoToEquiv (symIso (congIsoHelper x))))))
                            (λ i → rCancelₖ x i ≡ rCancelₖ x i) (p ∙ q))
          ∙ (λ i → transport (λ i → rCancelₖ x i ≡ rCancelₖ x i)
                              (transportRefl (congFunct (_+ₖ (-ₖ x)) p q i) i))
          ∙ (λ i → transport (λ i → rCancelₖ x i ≡ rCancelₖ x i) (
                              (lUnit (rUnit (transportRefl (cong (_+ₖ (-ₖ x)) p) (~ i)) i) i)
                              ∙ (lUnit (rUnit (transportRefl (cong (_+ₖ (-ₖ x)) q) (~ i)) i) i)))
          ∙ (λ i → transp (λ j → rCancelₖ x (i ∨ j) ≡ rCancelₖ x (i ∨ j)) i
                           (((λ j → rCancelₖ x (i ∧ (~ j))) ∙ transport refl (cong (_+ₖ (-ₖ x)) p) ∙ λ j → rCancelₖ x (i ∧ j))
                           ∙ (λ j → rCancelₖ x (i ∧ (~ j))) ∙ transport refl (cong (_+ₖ (-ₖ x)) q) ∙ λ j → rCancelₖ x (i ∧ j)))
          ∙ (λ i → transp (λ j → rCancelₖ x ((~ i) ∨ j) ≡ rCancelₖ x ((~ i) ∨ j)) (~ i)
                           ((λ j → rCancelₖ x ((~ i) ∧ (~ j))) ∙ transport refl (cong (_+ₖ (-ₖ x)) p) ∙ λ j → rCancelₖ x ((~ i) ∧ j))
                 ∙ transp (λ j → rCancelₖ x ((~ i) ∨ j) ≡ rCancelₖ x ((~ i) ∨ j)) (~ i)
                          ((λ j → rCancelₖ x ((~ i) ∧ (~ j))) ∙ transport refl (cong (_+ₖ (-ₖ x)) q) ∙ λ j → rCancelₖ x ((~ i) ∧ j)))
          ∙ (λ i → transport (λ j → rCancelₖ x j ≡ rCancelₖ x j)
                              (lUnit (rUnit (transport refl (cong (_+ₖ (-ₖ x)) p)) (~ i)) (~ i))
                 ∙ transport (λ j → rCancelₖ x j ≡ rCancelₖ x j)
                             (lUnit (rUnit (transport refl (cong (_+ₖ (-ₖ x)) q)) (~ i)) (~ i)))
          ∙ cong₂ (_∙_) (sym (substComposite (λ x → x) (isoToPath ((congIso (isoToEquiv (symIso (congIsoHelper x))))))
                                                                   (λ i → rCancelₖ x i ≡ rCancelₖ x i) p))
                        (sym (substComposite (λ x → x) (isoToPath ((congIso (isoToEquiv (symIso (congIsoHelper x))))))
                                                                   (λ i → rCancelₖ x i ≡ rCancelₖ x i) q))


  test2 : PathP (λ i → a north +ₖ ∣ north ∣ ≡ a (merid north i))
                (rUnitₖ (a north)) (rUnitₖ (a north) ∙ cong a (merid north))
  test2 i j =
    hcomp (λ k → λ { (i = i0) → rUnitₖ (a north) j
                    ; (j = i1) → a (merid north (i ∧ k))
                    ; (j = i0) → a north +ₖ ∣ north ∣})
          (rUnitₖ (a north) j)
----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.
coHomPushout≅coHomSn : (n m : ℕ) → grIso (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
morph.fun (grIso.fun (coHomPushout≅coHomSn n m)) =
  sRec setTruncIsSet
       λ f → ∣ (λ {(inl x) → f north
                 ; (inr x) → f south
                 ; (push a i) → f (merid a i)}) ∣₀
morph.ismorph (grIso.fun (coHomPushout≅coHomSn n m)) =
  sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ a b → cong ∣_∣₀ (funExt λ {(inl x) → refl
                                    ; (inr x) → refl
                                    ; (push a i) → refl })
morph.fun (grIso.inv (coHomPushout≅coHomSn n m)) =
  sRec setTruncIsSet
       (λ f → ∣ (λ {north → f (inl tt)
                  ; south → f (inr tt)
                  ; (merid a i) → f (push a i)}) ∣₀)
morph.ismorph (grIso.inv (coHomPushout≅coHomSn n m)) = 
  sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ a b → cong ∣_∣₀ (funExt λ {north → refl
                                    ; south → refl
                                    ; (merid a i) → refl })
grIso.rightInv (coHomPushout≅coHomSn n m) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f → cong ∣_∣₀ (funExt λ {(inl x) → refl
                                  ; (inr x) → refl
                                  ; (push a i) → refl })
grIso.leftInv (coHomPushout≅coHomSn n m) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f → cong ∣_∣₀ (funExt λ {north → refl
                                  ; south → refl
                                  ; (merid a i) → refl })


-------------------------- H⁰(S⁰) -----------------------------
S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a north = proj₁ a
S0→Int a south = proj₂ a

H⁰-S⁰≅ℤ×ℤ : grIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
H⁰-S⁰≅ℤ×ℤ =
  Iso'→Iso
    (iso'
      (iso (sRec (isOfHLevelProd 2 isSetInt isSetInt)
                 λ f → (f north) , (f south))
           (λ a → ∣ S0→Int a ∣₀)
           (λ { (a , b) → refl})
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → cong ∣_∣₀ (funExt (λ {north → refl ; south → refl}))))
      (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 isSetInt isSetInt) _ _)
              λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i))

------------------------ H⁰(S¹) ------------------------------

H⁰-S¹≅ℤ : grIso intGroup (coHomGr 0 (S₊ 1))
H⁰-S¹≅ℤ =
  Iso'→Iso
    (iso'
      (iso
        (λ a → ∣ (λ x → a) ∣₀)
        (sRec isSetInt (λ f → f north))
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
               λ f → cong ∣_∣₀ (funExt (suspToPropRec north (λ _ → isSetInt _ _) refl)))
        (λ a → refl))
      λ a b → cong ∣_∣₀ (funExt λ x → sym (addLemma a b)))
-----------------------------------------------------


H¹-S¹-helper : Iso (coHom 2 (S₊ 1)) Unit
H¹-S¹-helper =
  compIso (setTruncIso S1→K2≡K2×K1)
    (compIso
      setTruncOfProdIso
      (compIso
        (prodIso setTruncTrunc0Iso setTruncTrunc0Iso)
        (pathToIso
          ((λ i → isContr→≡Unit helper2 i × isContr→≡Unit helper3 i)
           ∙ sym diagonal-unit))))
  where

  helper2 : isContr (hLevelTrunc 2 (hLevelTrunc 4 (S₊ 2)))
  helper2 =
    transport (λ i → isContr (isoToPath (truncOfTruncIso {A = (S₊ 2)} 2 2) i))
              (isConnectedSubtr 2 1 (sphereConnected 2))

  helper3 : isContr (hLevelTrunc 2 (hLevelTrunc 3 (S₊ 1)))
  helper3 =
    transport (λ i → isContr (hLevelTrunc 2 (truncIdempotent {A = S₊ 1} 3 isGroupoidS1 (~ i))))
              (sphereConnected 1)

--------------------------------------------------------------------

--------------------------H¹(S¹) -----------------------------------
H¹-S¹≅ℤ : grIso intGroup (coHomGr 1 (S₊ 1))
H¹-S¹≅ℤ =
  compGrIso
    (diagonalIso1
      _
      (coHomGr 0 (S₊ 0))
      _
      (invGrIso H⁰-S⁰≅ℤ×ℤ)
      (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
      (λ x → MV.Ker-i⊂Im-d _ _(S₊ 0) (λ _ → tt) (λ _ → tt) 0 x
                           (×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)
                               (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)))
      (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
             (λ x inker
                   → pRec propTruncIsProp
                           (λ {((f , g) , id') → helper x f g id' inker})
                           ((MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀ inker))))
      (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
             λ F surj
               → pRec (setTruncIsSet _ _)
                       (λ { (x , id) → MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ ∣
                                 (∣ (λ _ → x) ∣₀ , ∣ (λ _ → 0) ∣₀) ,
                                              (cong ∣_∣₀ (funExt (surjHelper x))) ∙ sym id ∣₋₁ }) surj) )
    (invGrIso (coHomPushout≅coHomSn 0 1))
                                              
  where
  surjHelper :  (x : Int) (x₁ : S₊ 0) → x +ₖ (-ₖ pos 0) ≡ S0→Int (x , x) x₁
  surjHelper x north = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x
  surjHelper x south = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x

  helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₀) (id : morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₀)
         → isInKer (coHomGr 0 (S₊ 0))
                    (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                    (morph.fun (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0))
                    ∣ F ∣₀
         → ∃[ x ∈ Int ] ∣ F ∣₀ ≡ morph.fun (grIso.inv H⁰-S⁰≅ℤ×ℤ) (x , x)
  helper F =
    sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f g id inker
             → pRec propTruncIsProp
                     (λ {((a , b) , id2)
                        → sElim2 {B = λ f g → morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₀ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₋₁)
                                  a b id2})
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] morph.fun (grIso.inv H⁰-S⁰≅ℤ×ℤ) (x , x)
             ≡ morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (∣ f ∣₀ , ∣ g ∣₀)
    helper2 f g = (f _ +ₖ (-ₖ g _) ) , cong ∣_∣₀ (funExt (λ {north → refl ; south → refl})) 


---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------
coHom-n-Sn : (n : ℕ) → grIso intGroup (coHomGr (suc n) (S₊ (suc n)))
coHom-n-Sn zero = H¹-S¹≅ℤ
coHom-n-Sn (suc n) =
  compGrIso
    (compGrIso
      (coHom-n-Sn n)
      theIso)
    (invGrIso (coHomPushout≅coHomSn (suc n) (suc (suc n))))
  where
  theIso : grIso (coHomGr (suc n) (S₊ (suc n))) (coHomGr (suc (suc n))
                 (Pushout {A = S₊ (suc n)} (λ _ → tt) (λ _ → tt)))
  theIso =
    SES→Iso
      (×coHomGr (suc n) Unit Unit)
      (×coHomGr (suc (suc n)) Unit Unit)
      (ses (λ p q → ×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (proj₁ p) (proj₁ q))
                        (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (proj₂ p) (proj₂ q)))
           (λ p q → ×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (proj₁ p) (proj₁ q))
                        (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (proj₂ p) (proj₂ q)))
           (MV.Δ _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.i _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (2 + n))
           (MV.d _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.Ker-d⊂Im-Δ _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.Ker-i⊂Im-d _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n)))
--------------------------------------------------------------------


------------------------- H¹(S⁰) ≅ 0 -------------------------------
H¹-S⁰≅0 : grIso (coHomGr 1 (S₊ 0)) trivialGroup 
H¹-S⁰≅0 =
  Iso'→Iso
    (iso'
      (iso (λ _ → tt)
           (λ _ → 0ₕ)
           (λ _ → refl)
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → pRec (setTruncIsSet _ _)
                              (λ id → cong ∣_∣₀ (sym id))
                              (helper f (f north) (f south) refl refl)))
      λ _ _ → refl)
  where
   helper : (f : S₊ 0 → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1) → (x y : ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1) → (f north ≡ x) → (f south ≡ y) → ∥ f ≡ (λ _ → 0ₖ) ∥₋₁
   helper f =
     elim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 propTruncIsProp)
           (suspToPropRec2 north (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → propTruncIsProp)
           λ id id2 → ∣ funExt (λ {north → id ; south → id2}) ∣₋₁) 

------------------------- H²(S¹) ≅ 0 -------------------------------
H²-S¹≅0 : grIso (coHomGr 2 (S₊ 1)) trivialGroup
H²-S¹≅0 =
  Iso'→Iso
    (iso'
      (iso
        (λ _ → tt)
        (λ _ → 0ₕ)
        (λ _ → refl)
        (λ _ → isPropH¹-S¹≅ℤ _ _))
      λ _ _ → refl)
  where
  isPropH¹-S¹≅ℤ : isProp (coHom 2 (S₊ 1))
  isPropH¹-S¹≅ℤ =
    isOfHLevelSuc 0
      (transport (λ i → isContr (isoToPath H¹-S¹-helper (~ i)))
                 isContrUnit)
-------------------------------------------------------------------


--------- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

S¹map : hLevelTrunc 3 S¹ → S¹
S¹map = trElim (λ _ → isGroupoidS¹) (idfun S¹)

S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
S¹map-id = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl

S1map : hLevelTrunc 3 (S₊ 1) → (S₊ 1)
S1map = trElim (λ _ → isGroupoidS1) (idfun _)




S¹→S¹ : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × Int)
Iso.fun S¹→S¹ f = S¹map (f base)
                 , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
Iso.inv S¹→S¹ (s , int) base = ∣ s ∣
Iso.inv S¹→S¹ (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
Iso.rightInv S¹→S¹ (s , int) = ×≡ refl ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                       ∙ windingIntLoop int)
Iso.leftInv S¹→S¹ f = funExt λ { base → S¹map-id (f base)
                               ; (loop i) j → helper2 j i}
  where
  helper2 : PathP (λ i → S¹map-id (f base) i ≡ S¹map-id (f base) i)
                  (λ i → ∣ basechange2 (S¹map (f base)) (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁)))))) i ∣)
                  (cong f loop)
  helper2 i j = 
    hcomp (λ k → λ { (i = i0) → cong ∣_∣ (basechange2 (S¹map (f base)) (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁))))))) j
                    ; (i = i1) → S¹map-id (f (loop j)) k
                    ; (j = i0) → S¹map-id (f base) (i ∧ k)
                    ; (j = i1) → S¹map-id (f base) (i ∧ k)})
          (helper4 i j)
    where
    helper4 : Path (Path (hLevelTrunc 3 _) _ _)
                   (cong ∣_∣ (basechange2 (S¹map (f base))
                                         (intLoop
                                           (winding
                                             (basechange2⁻ (S¹map (f base))
                                                           (λ i₁ → S¹map (f (loop i₁))))))))
                   λ i → ∣ S¹map (f (loop i)) ∣
    helper4 i =
      cong ∣_∣
           ((cong (basechange2 (S¹map (f base)))
                   (decodeEncode base (basechange2⁻ (S¹map (f base))
                                                    (λ i₁ → S¹map (f (loop i₁)))))
            ∙ basechange2-sect (S¹map (f base))
                               (λ i → S¹map (f (loop i)))) i)

S1→S1→S1×Int : Iso ((S₊ 1) → hLevelTrunc 3 (S₊ 1)) ((hLevelTrunc 3 (S₊ 1)) × Int)
S1→S1→S1×Int = compIso helper2 (compIso S¹→S¹ helper)
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

S¹→S¹≡S1→S1 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
Iso.fun S¹→S¹≡S1→S1 f x = trMap S1→S¹ (f (S¹→S1 x))
Iso.inv S¹→S¹≡S1→S1 f x = trMap S¹→S1 (f (S1→S¹ x))
Iso.rightInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-sect x i)) i
  where
  helper2 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-sect a)
Iso.leftInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-retr x i)) i
  where
  helper2 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-retr a)




basechange-lemma : ∀ {ℓ} {A : Type ℓ} {a : A} (x y : S¹) (F : a ≡ a → S¹) (f : S¹ → a ≡ a) (g : S¹ → a ≡ a)
                  → (f base ≡ refl)
                  → (g base ≡ refl)
                  → basechange2⁻ (F (f base ∙ g base)) (cong₂ {A = S¹} {B = λ x → S¹} (λ x y → F (f x ∙ g y)) loop loop)
                   ≡ basechange2⁻ (F (f base)) (cong (λ x → F (f x)) loop) ∙ basechange2⁻ (F (g base)) (cong (λ x → F (g x)) loop)
basechange-lemma x y F f g frefl grefl  =
    (λ i → basechange2⁻ (F (f base ∙ g base)) (cong₂Funct (λ x y → F (f x ∙ g y)) loop loop i))
  ∙ (λ i → basechange2⁻ (F (f base ∙ g base)) (cong (λ x₁ → F (f x₁ ∙ g base)) loop ∙ cong (λ y₁ → F (f base ∙ g y₁)) loop))
  ∙ basechange2⁻-morph (F (f base ∙ g base)) _ _
  ∙ (λ j → basechange2⁻ (F (f base ∙ grefl j))
                        (λ i → F (f (loop i) ∙ grefl j))
          ∙ basechange2⁻ (F (frefl j ∙ g base))
                        (λ i → F (frefl j ∙ g (loop i))))
  ∙ ((λ j → basechange2⁻ (F (rUnit (f base) (~ j)))
                        (λ i → F (rUnit (f (loop i)) (~ j)))
          ∙ basechange2⁻ (F (lUnit (g base) (~ j)))
                        (λ i → F (lUnit (g (loop i)) (~ j)))))



coHom1S1≃ℤ : grIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ =
  Iso'→Iso
    (iso'
      (iso
        (sRec isSetInt (λ f → proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f))))
        (λ a → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a)) ∣₀)
         (λ a → (λ i → proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a))))))
              ∙ (λ i → proj₂ (Iso.fun S¹→S¹ (Iso.rightInv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , a)) i)))
              ∙ λ i → proj₂ (Iso.rightInv S¹→S¹ (base , a) i)) 
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
               λ f → (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹ (base , proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
                    ∙ (λ i → sRec setTruncIsSet
                                  (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₀)
                                  (sRec setTruncIsSet
                                        (λ x → ∣ Iso.inv S¹→S¹ (x , (proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
                                        ∣ base ∣₀))
                    ∙ (λ i → sRec setTruncIsSet
                                  (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₀)
                                  (sRec setTruncIsSet
                                        (λ x → ∣ Iso.inv S¹→S¹ (x , (proj₂ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
                                        (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (proj₁ (Iso.fun S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f)))) i)))
                    ∙ (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.leftInv S¹→S¹ (Iso.fun S¹→S¹≡S1→S1 f) i) ∣₀)
                    ∙ (λ i → ∣ Iso.leftInv S¹→S¹≡S1→S1 f i ∣₀)))
      (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
              λ f g → (λ i → winding (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))))
                                       (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))))
                    ∙ cong winding (helper2 (f (S¹→S1 base)) (g (S¹→S1 base)) f g refl refl)
                    ∙ winding-hom ((basechange2⁻ (S¹map (trMap S1→S¹ (f north)))
                                                 (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))))
                                   ((basechange2⁻ (S¹map (trMap S1→S¹ (g north)))
                                                 (λ i → S¹map (trMap S1→S¹ (g (S¹→S1 (loop i)))))))))


  where
  helper2 : (x y : hLevelTrunc 3 (S₊ 1)) (f g : S₊ 1 → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1)
        → (f (S¹→S1 base)) ≡ x
        → (g (S¹→S1 base)) ≡ y
        → (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base)))))))
                        (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))
          ≡ (basechange2⁻ (S¹map (trMap S1→S¹ ((f (S¹→S1 base))))))
                          (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))
          ∙ (basechange2⁻ (S¹map (trMap S1→S¹ ((g (S¹→S1 base)))))
                          (λ i → S¹map (trMap S1→S¹ ((g (S¹→S1 (loop i)))))))
  helper2 = elim2
             (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3
                 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3
                     λ _ → isOfHLevelPath 3 (isOfHLevelSuc 3 (isGroupoidS¹) base base) _ _)
             (suspToPropRec2 {A = S₊ 0} north
                  (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → (isGroupoidS¹) _ _ _ _ )
                  λ f g reflf reflg →
                 (basechange-lemma
                    base
                    base
                    (λ x → S¹map (trMap S1→S¹ (ΩKn+1→Kn x)))
                    (λ x → Kn→ΩKn+1 1 (f (S¹→S1 x))) ((λ x → Kn→ΩKn+1 1 (g (S¹→S1 x))))
                    (cong (Kn→ΩKn+1 1) reflf ∙ Kn→ΩKn+10ₖ 1)
                    (cong (Kn→ΩKn+1 1) reflg ∙ Kn→ΩKn+10ₖ 1))
               ∙ λ j → basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 base)) j)))
                                     (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 (loop i))) j)))
                      ∙ basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 base)) j)))
                                     (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 (loop i))) j))))
