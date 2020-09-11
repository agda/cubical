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
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; map to trMap ; rec to trRec)

infixr 33 _⋄_

_⋄_ : _
_⋄_ = compIso

0₀ = 0ₖ 0
0₁ = 0ₖ 1
0₂ = 0ₖ 2
0₃ = 0ₖ 3
0₄ = 0ₖ 4

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
                  λ a i → ∣(S1→S¹-sect a) i ∣
Iso.leftInv S1→S1≡S¹→S¹ F = funExt λ x i → helper2 (F (S1→S¹-retr x i)) i
  where
  helper2 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a i → ∣(S1→S¹-retr a i) ∣

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
    helper2 i j =
         ∣ ((cong (basechange2 (S¹map (f base)))
                   (decodeEncode base (basechange2⁻ (S¹map (f base))
                                                    (λ i₁ → S¹map (f (loop i₁)))))
            ∙ basechange2-sect (S¹map (f base))
                               (λ i → S¹map (f (loop i)))) i) j ∣

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
           (λ a → ΣPathP ((λ i → ∣ S1→S¹-retr a i ∣) , refl))
           s
  Iso.leftInv helper (s , int) = ΣPathP ((S1→S¹-sect s) ,  refl)

  helper2 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
  Iso.fun helper2 f x = trMap S1→S¹ (f (S¹→S1 x))
  Iso.inv helper2 f x = trMap S¹→S1 (f (S1→S¹ x))
  Iso.rightInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-sect x i)) i
    where
    helper3 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
    helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                     λ a i → ∣ (S1→S¹-sect a) i ∣
  Iso.leftInv helper2 f = funExt λ x i → helper3 (f (S1→S¹-retr x i)) i
    where
    helper3 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
    helper3 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                     λ a i → ∣ (S1→S¹-retr a) i ∣


module _ (key : Unit') where
  module P = lockedCohom key
  _+K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
  _+K_ {n = n} = P.+K n

  -K_ : {n : ℕ} → coHomK n → coHomK n
  -K_ {n = n} = P.-K n

  infixr 55 _+K_
  infixr 55 -K_

  {- Proof that S¹→K2 is isomorphic to K2×K1 (as types). Needed for H²(T²)  -}
  S1→K2≡K2×K1' : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
  Iso.fun S1→K2≡K2×K1' f = (f north , ΩKn+1→Kn (sym (P.rCancelK 2 (f north))
                                                          ∙ (λ i → f (merid south i) +K (-K f (merid north i)))
                                                          ∙ P.rCancelK 2 (f south)))
  Iso.inv S1→K2≡K2×K1' (a , b) north = a +K 0₂ -- a +ₖ 0₂
  Iso.inv S1→K2≡K2×K1' (a , b) south = a +K 0₂ -- a +ₖ 0₂
  Iso.inv S1→K2≡K2×K1' (a , b) (merid south i) = a +K (Kn→ΩKn+1 1 b i)
  Iso.inv S1→K2≡K2×K1' (a , b) (merid north i) = a +K 0₂
  Iso.rightInv S1→K2≡K2×K1' (a , b) = ΣPathP ((P.rUnitK 2 a) , cong ΩKn+1→Kn (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +K x) +K (-K (a +K 0₂))) (funExt (λ x → sym (cancelHelper a x))) (P.rCancelK 2 (a +K 0₂))) ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 1) b)
      module _ where
      cancelHelper : (a b : coHomK 2) → (a +K b) +K (-K (a +K 0₂)) ≡ b
      cancelHelper a b =
        (a +K b) +K (-K (a +K (0ₖ _)))      ≡⟨ (λ i → (a +K b) +K (-K (P.rUnitK _ a i))) ⟩≡⟨ cong (_+K (-K a)) (P.commK _ a b) ⟩
        (b +K a) +K (-K a)             ≡⟨ P.assocK _ b a (-K a) ⟩≡⟨ cong (b +K_) (P.rCancelK _ a) ⟩
        (b +K 0₂                       ≡⟨ P.rUnitK _ b ⟩
        b ∎)

      congHelper2 : (p : 0₂ ≡ 0₂) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) → (q : (f 0₂) ≡ 0₂)
                  → (sym q) ∙ cong f p ∙ q ≡ p
      congHelper2 p f = J (λ f _ → (q : (f 0₂) ≡ 0₂) → (sym q) ∙ cong f p ∙ q ≡ p)
                         λ q → (cong (sym q ∙_) (isCommΩK 2 p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
                              ∙ sym (lUnit p)

  Iso.leftInv S1→K2≡K2×K1' a =
    funExt λ {north → P.rUnitK _ (a north)
            ; south → P.rUnitK _ (a north) ∙ cong a (merid north)
            ; (merid south i) → m-south i
            ; (merid north i) → m-north i}
    where

    m-north : PathP (λ i → a north +K ∣ north ∣ ≡ a (merid north i))
                  (P.rUnitK _ (a north)) (P.rUnitK _ (a north) ∙ cong a (merid north))
    m-north i j =
      hcomp (λ k → λ { (i = i0) → P.rUnitK _ (a north) j
                     ; (j = i1) → a (merid north (i ∧ k))
                     ; (j = i0) → a north +K ∣ north ∣})
            (P.rUnitK _ (a north) j)


    m-south : PathP (λ i → a north +K Kn→ΩKn+1 1 (ΩKn+1→Kn ((sym (P.rCancelK _ (a north))
                           ∙ (λ i → a (merid south i) +K (-K a (merid north i)))
                           ∙ P.rCancelK _ (a south)))) i ≡ a (merid south i)) (P.rUnitK _ (a north)) (P.rUnitK _ (a north) ∙ cong a (merid north))
    m-south j i =
      hcomp (λ k → λ { (i = i0) → (helper ∙∙ together ∙∙ congFunct (_+K 0₂) (cong a (merid south)) (cong a (sym (merid north)))) (~ k) j
                     ; (i = i1) → a (merid south j)
                     ; (j = i0) → P.rUnitK _ (a north) i
                     ; (j = i1) → ((λ j → P.rUnitK _ (a (merid north ((~ k) ∧ j))) (j ∧ k)) ∙ λ j → P.rUnitK _ (a (merid north ((~ k) ∨ j))) (k ∨ j)) i })
           (hcomp (λ k → λ { (i = i1) → a (merid south j)
                            ; (i = i0) → compPath-filler ((cong (λ x → a x +K 0₂) (merid south))) (cong (λ x → a x +K 0₂) (sym (merid north))) k j
                            ; (j = i0) → P.rUnitK _ (a north) i
                            ; (j = i1) → pathFiller2 (cong (_+K 0₂) (cong a (merid north))) (P.rUnitK _ (a south)) k i})
                   (P.rUnitK _ (a (merid south j)) i))


      where
      pathFiller : (P.rUnitK _ (a north) ∙ cong a (merid north)) ≡ cong (_+K 0₂) (cong a (merid north)) ∙ P.rUnitK _ (a south)
      pathFiller = (λ i → (λ j → P.rUnitK _ (a (merid north (i ∧ j))) (j ∧ (~ i)))
                  ∙ λ j → P.rUnitK _ (a (merid north (i ∨ j))) (~ i ∨ j))

      pathFiller2 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
      pathFiller2 p q i =
        hcomp (λ k → λ { (i = i0) → lUnit q (~ k)
                       ; (i = i1) → p ∙ q})
              ((λ j → p (~ i ∨ j)) ∙ q)

      helper : Path (_ ≡ _) (λ i → a north +K Kn→ΩKn+1 1 (ΩKn+1→Kn ((sym (P.rCancelK _ (a north))
                           ∙ (λ i → a (merid south i) +K (-K a (merid north i)))
                           ∙ P.rCancelK _ (a south)))) i)
                            ---
                            (cong (a north +K_) (sym (P.rCancelK _ (a north)))
                           ∙ ((λ j → (a north) +K (a (merid south j)) +K (-K (a north)))
                             ∙ λ j → a north +K a (merid north (~ j)) +K (-K (a north)))
                           ∙ cong (a north +K_) (P.rCancelK _ (a north)))
      helper = (λ j i → a north +K Iso.rightInv (Iso3-Kn-ΩKn+1 1) (sym (P.rCancelK _ (a north))
                           ∙ (λ i → a (merid south i) +K (-K a (merid north i)))
                           ∙ P.rCancelK _ (a south)) j i)
            ∙∙ congFunct (λ x → a north +K x) (sym (P.rCancelK _ (a north))) ((λ i → a (merid south i) +K (-K a (merid north i))) ∙ P.rCancelK _ (a south))
            ∙∙ ((λ j → cong (a north +K_) (sym (P.rCancelK _ (a north)))
                ∙ congFunct (λ x → a north +K x) ((λ i → a (merid south i) +K (-K a (merid north i)))) (P.rCancelK _ (a south)) j)
            ∙∙ ((λ j → cong (a north +K_) (sym (P.rCancelK _ (a north)))
                ∙ cong₂Funct (λ x y → a north +K a x +K (-K (a y))) (merid south) (merid north) j ∙ cong (λ x → a north +K x) ((P.rCancelK _ (a south)))))
            ∙∙ (λ i → cong (a north +K_) (sym (P.rCancelK _ (a north)))
                 ∙ ((λ j → a north +K a (merid south j) +K (-K (a north)))
                 ∙ λ j → a north +K a (merid north (~ i ∨ (~ j))) +K (-K (a (merid north (j ∧ (~ i))))))
                 ∙ cong (a north +K_) ((P.rCancelK _ (a (merid north (~ i)))))))

      pathHelper : (a b : hLevelTrunc 4 (S₊ 2)) → a +K b +K (-K a) ≡ b +K 0₂
      pathHelper a b =
          a +K b +K (-K a)     ≡⟨ P.commK _ a (b +K (-K a)) ⟩≡⟨ P.assocK _ b (-K a) a ⟩
          (b +K (-K a) +K a     ≡⟨ cong (b +K_) (P.lCancelK _ a) ⟩
           b +K 0₂ ∎)

      helperFun : ∀ {ℓ} {A : Type ℓ} {a b : A} (p' p : a ≡ b) (q q' : b ≡ b) (r : a ≡ a)
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

      together : Path (_ ≡ _) (cong (λ x → a north +K x) (sym (P.rCancelK _ (a north)))
                             ∙ ((λ j → a north +K ((a (merid south j)) +K (-K (a north)))) ∙ λ j → a north +K ((a (merid north (~ j))) +K (-K (a north))))
                             ∙ cong (λ x → a north +K x) (P.rCancelK _ (a north)))
                              (cong(λ y → y +K 0₂) (cong a (merid south) ∙ cong a (sym (merid north))))
      together =
        helperFun (λ i → pathHelper (a north) (a north) (~ i))
                  (cong (a north +K_) (sym (P.rCancelK _ (a north))))
                  ((λ j → a north +K a (merid south j) +K (-K (a north))) ∙ λ j → a north +K a (merid north (~ j)) +K (-K (a north)))
                  (((λ j → a north +K a (merid south j) +K (-K (a north))) ∙ λ j → a north +K a (merid north (~ j)) +K (-K (a north))))
                  (cong(_+K 0₂) (cong a (merid south) ∙ cong a (sym (merid north))))
                  (isCommΩK-based 2 _)
                  refl
                  λ i → hcomp (λ k → λ {(i = i0) → (λ j → a north +K a (merid south j) +K (-K (a north)))
                                                    ∙ λ j → a north +K a (merid north (~ j)) +K (-K (a north))
                                        ; (i = i1) → congFunct (_+K 0₂) (cong a (merid south)) (cong a (sym (merid north))) (~ k)})
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

S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
S1→K2≡K2×K1 = S1→K2≡K2×K1' tt*
