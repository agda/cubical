{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Prelims where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)


infixr 33 _⋄_

_⋄_ : _
_⋄_ = compIso


S¹map : hLevelTrunc 3 S¹ → S¹
S¹map = trRec isGroupoidS¹ (idfun _)

S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
S¹map-id = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl

S1map : hLevelTrunc 3 (S₊ 1) → (S₊ 1)
S1map = trRec isGroupoidS1 (idfun _)

S1→S1≡S¹→S¹ : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
Iso.fun S1→S1≡S¹→S¹ f x = trMap S1→S¹ (f (S¹→S1 x))
Iso.inv S1→S1≡S¹→S¹ f x = trMap S¹→S1 (f (S1→S¹ x))
Iso.rightInv S1→S1≡S¹→S¹ F = funExt λ x i → helper2 (F (S1→S¹-sect x i)) i
  where
  helper2 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-sect a)
Iso.leftInv S1→S1≡S¹→S¹ F = funExt λ x i → helper2 (F (S1→S¹-retr x i)) i
  where
  helper2 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-retr a)

{- Proof that (S¹ → ∥ S¹ ∥₁) ≃ S¹ × ℤ. Needed for H¹(S¹)) -}
-- We prove that (S¹ → ∥ S¹ ∥) ≃ S¹ × ℤ. Note that the truncation doesn't really matter, since S¹ is a groupoid.
-- Given a map f : S¹ → S¹, the idea is to send this to (f(base) , winding (f(loop))). For this to be
-- well-typed, we need to translate f(loop) into an element in Ω(S¹,base).
S¹→S¹≡S¹×Int : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × Int)
Iso.fun S¹→S¹≡S¹×Int f = S¹map (f base)
                 , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
Iso.inv S¹→S¹≡S¹×Int (s , int) base = ∣ s ∣
Iso.inv S¹→S¹≡S¹×Int (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
Iso.rightInv S¹→S¹≡S¹×Int (s , int) = ΣPathP (refl , ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                                      ∙ windingIntLoop int))
Iso.leftInv S¹→S¹≡S¹×Int f = funExt λ { base → S¹map-id (f base)
                                      ; (loop i) j → helper j i}
  where
  helper : PathP (λ i → S¹map-id (f base) i ≡ S¹map-id (f base) i)
                  (λ i → ∣ basechange2 (S¹map (f base))
                             (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁)))))) i ∣)
                  (cong f loop)
  helper i j =
    hcomp (λ k → λ { (i = i0) → cong ∣_∣ (basechange2 (S¹map (f base))
                                           (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁))))))) j
                    ; (i = i1) → S¹map-id (f (loop j)) k
                    ; (j = i0) → S¹map-id (f base) (i ∧ k)
                    ; (j = i1) → S¹map-id (f base) (i ∧ k)})
          (helper2 i j)
    where
    helper2 : Path (Path (hLevelTrunc 3 _) _ _)
                   (cong ∣_∣ (basechange2 (S¹map (f base))
                                         (intLoop
                                           (winding
                                             (basechange2⁻ (S¹map (f base))
                                                           (λ i₁ → S¹map (f (loop i₁))))))))
                   λ i → ∣ S¹map (f (loop i)) ∣
    helper2 i =
      cong ∣_∣
           ((cong (basechange2 (S¹map (f base)))
                   (decodeEncode base (basechange2⁻ (S¹map (f base))
                                                    (λ i₁ → S¹map (f (loop i₁)))))
            ∙ basechange2-sect (S¹map (f base))
                               (λ i → S¹map (f (loop i)))) i)


{- Proof that (S¹ → K₁) ≃ K₁ × ℤ. Needed for H¹(T²) -}
S1→K₁≡S1×Int : Iso ((S₊ 1) → coHomK 1) (coHomK 1 × Int)
S1→K₁≡S1×Int = helper2 ⋄ S¹→S¹≡S¹×Int ⋄ helper
  where
  helper : Iso (S¹ × Int) (hLevelTrunc 3 (S₊ 1) × Int)
  Iso.fun helper (s , int) = ∣ S¹→S1 s  ∣ , int
  Iso.inv helper (s , int) = (S1→S¹ (S1map s)) , int
  Iso.rightInv helper (s , int) =
    trElim {B = λ s → (∣ S¹→S1 (S1→S¹ (S1map s)) ∣ , int) ≡ (s , int)}
           (λ _ → isOfHLevelPath 3 (isOfHLevelΣ 3 (isOfHLevelTrunc 3) (λ _ → isOfHLevelSuc 2 isSetInt)) _ _)
           (λ a → ΣPathP ((cong ∣_∣ (S1→S¹-retr a)) , refl))
           s
  Iso.leftInv helper (s , int) = ΣPathP ((S1→S¹-sect s) ,  refl)

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
  ΣPathP ((rUnitₖ a) ,
     ((cong ΩKn+1→Kn (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +ₖ x) +ₖ (-ₖ (a +ₖ 0ₖ))) (funExt (λ x → sym (cancelHelper a x))) (rCancelₖ (a +ₖ 0ₖ))))
    ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 1) b))
    module _ where
    cancelHelper : (a b : hLevelTrunc 4 (S₊ 2)) → (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ)) ≡ b
    cancelHelper a b =
      (a +ₖ b) +ₖ (-ₖ (a +ₖ 0ₖ))      ≡⟨ (λ i → (a +ₖ b) +ₖ (-ₖ (rUnitₖ a i))) ⟩≡⟨ cong (λ x → x +ₖ (-ₖ a)) (commₖ a b) ⟩
      (b +ₖ a) +ₖ (-ₖ a)             ≡⟨ assocₖ b a (-ₖ a) ⟩≡⟨ cong (λ x → b +ₖ x) (rCancelₖ a) ⟩
      (b +ₖ 0ₖ                       ≡⟨ rUnitₖ b ⟩
      b ∎)

    congHelper2 : (p : 0ₖ ≡ 0ₖ) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) → (q : (f 0ₖ) ≡ 0ₖ)
                → (sym q) ∙ cong f p ∙ q ≡ p
    congHelper2 p f = J (λ f _ → (q : (f 0ₖ) ≡ 0ₖ) → (sym q) ∙ cong f p ∙ q ≡ p)
                       λ q → (cong (sym q ∙_) (isCommΩK 2 p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
                            ∙ sym (lUnit p)

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

    helperFun : ∀ {ℓ} {A : Type ℓ} {a b : A} (p' p : a ≡ b) (q q' : b ≡ b) (r : a ≡ a) -- (p p' : a ≡ b) (q q' : b ≡ b) (r : a ≡ a)
             → ((p q : a ≡ a) → p ∙ q ≡ q ∙ p)
             → q ≡ q'
             → PathP (λ i → p' (~ i) ≡ p' (~ i)) q' r
             → p ∙ q ∙ sym p ≡ r
    helperFun {a = a} {- p p' q q' r comm qid dep -} =
      J (λ b p' → (p : a ≡ b) → (q q' : b ≡ b) → (r : a ≡ a) -- (p p' : a ≡ b) (q q' : b ≡ b) (r : a ≡ a)
                 → ((p q : a ≡ a) → p ∙ q ≡ q ∙ p)
                 → q ≡ q'
                 → PathP (λ i → p' (~ i) ≡ p' (~ i)) q' r
                 → p ∙ q ∙ sym p ≡ r)
         λ p q q' r comm id id2 → (cong (λ x → p ∙ x ∙ (sym p)) (id ∙ id2)
                                 ∙∙ cong (p ∙_) (comm _ _)
                                 ∙∙ assoc _ _ _)
                                 ∙∙ cong (_∙ r) (rCancel _)
                                 ∙∙ sym (lUnit r)
    {-
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
      r ∎ -}

    together : Path (_ ≡ _) (cong (a north +ₖ_) (sym (rCancelₖ (a north)))
                           ∙ ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                           ∙ cong (a north +ₖ_) (rCancelₖ (a north)))
                            (cong(_+ₖ 0ₖ) (cong a (merid south) ∙ cong a (sym (merid north))))
    together =
      helperFun (λ i → pathHelper (a north) (a north) (~ i))
                (cong (a north +ₖ_) (sym (rCancelₖ (a north))))
                ((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north)))
                (((λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north))) ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north))))
                (cong(_+ₖ 0ₖ) (cong a (merid south) ∙ cong a (sym (merid north))))
                (isCommΩK-based 2 _)
                refl
                λ i → hcomp (λ k → λ {(i = i0) → (λ j → a north +ₖ a (merid south j) +ₖ (-ₖ (a north)))
                                                  ∙ λ j → a north +ₖ a (merid north (~ j)) +ₖ (-ₖ (a north))
                                      ; (i = i1) → congFunct (_+ₖ 0ₖ) (cong a (merid south)) (cong a (sym (merid north))) (~ k)})
                             ((λ j → pathHelper (a north) (a (merid south j)) i) ∙ (λ j → pathHelper (a north) (a (merid north (~ j))) i))




-- The translation mention above uses the basechange function.

---------- lemmas on the baschange of ΩS¹ ----------

--The following lemma is used to prove the basechange2⁻ preserves
-- path composition (in a more general sense than what is proved in basechange2⁻-morph)

basechange-lemma : ∀ {ℓ} {A : Type ℓ} {a : A} (x y : S¹) (F : a ≡ a → S¹) (f : S¹ → a ≡ a) (g : S¹ → a ≡ a)
                  → (f base ≡ refl)
                  → (g base ≡ refl)
                  → basechange2⁻ (F (f base ∙ g base)) (cong₂ {A = S¹} {B = λ x → S¹} (λ x y → F (f x ∙ g y)) loop loop)
                   ≡ basechange2⁻ (F (f base)) (cong (λ x → F (f x)) loop) ∙ basechange2⁻ (F (g base)) (cong (λ x → F (g x)) loop)
basechange-lemma x y F f g frefl grefl  =
    ((λ i → basechange2⁻ (F (f base ∙ g base)) (cong₂Funct (λ x y → F (f x ∙ g y)) loop loop i))
  ∙∙ (λ i → basechange2⁻ (F (f base ∙ g base)) (cong (λ x₁ → F (f x₁ ∙ g base)) loop ∙ cong (λ y₁ → F (f base ∙ g y₁)) loop))
  ∙∙ basechange2⁻-morph (F (f base ∙ g base)) _ _)
  ∙∙ (λ j → basechange2⁻ (F (f base ∙ grefl j))
                        (λ i → F (f (loop i) ∙ grefl j))
          ∙ basechange2⁻ (F (frefl j ∙ g base))
                        (λ i → F (frefl j ∙ g (loop i))))
  ∙∙ ((λ j → basechange2⁻ (F (rUnit (f base) (~ j)))
                        (λ i → F (rUnit (f (loop i)) (~ j)))
          ∙ basechange2⁻ (F (lUnit (g base) (~ j)))
                        (λ i → F (lUnit (g (loop i)) (~ j)))))


basechange-lemma2 : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹)
                 → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                  ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                  ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
basechange-lemma2 f g F = coInd (f base) (g base) refl refl
  where
  coInd : (x y : hLevelTrunc 3 (S₊ 1))
                   → f base ≡ x
                   → g base ≡ y
                   → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                    ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                    ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
  coInd =
    elim2 (λ _ _ → isGroupoidΠ2 λ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isGroupoidS¹ base base)) _ _ )
          (suspToPropRec2 north (λ _ _ → isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _)
              λ fb gb → basechange-lemma base base (F ∘ ΩKn+1→Kn) (Kn→ΩKn+1 1 ∘ f) (Kn→ΩKn+1 1 ∘ g)
                                          (cong (Kn→ΩKn+1 1) fb ∙ Kn→ΩKn+10ₖ 1)
                                          (cong (Kn→ΩKn+1 1) gb ∙ Kn→ΩKn+10ₖ 1)
                       ∙ cong₂ (_∙_) (λ j i → basechange2⁻ (F (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f base) j))
                                                            (cong (λ x → F (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f x) j)) loop) i)
                                     λ j i → basechange2⁻ (F (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g base) j))
                                                              (cong (λ x → F (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g x) j)) loop) i)
