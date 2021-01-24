{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.ZCohomologyOld.Groups.Prelims where

open import Cubical.ZCohomology.Base
open import Cubical.Experiments.ZCohomologyOld.Properties
open import Cubical.Experiments.ZCohomologyOld.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Homotopy.Loopspace

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
S1map = trRec isGroupoidS¹ (idfun _)


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
S1→K₁≡S1×Int = S¹→S¹≡S¹×Int ⋄ prodIso (invIso (truncIdempotentIso 3 (isGroupoidS¹))) idIso
module _ (key : Unit') where
  module P = lockedCohom key
  private
    _+K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
    _+K_ {n = n} = P.+K n

    -K_ : {n : ℕ} → coHomK n → coHomK n
    -K_ {n = n} = P.-K n

    _-K_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
    _-K_ {n = n} = P.-Kbin n

  infixr 55 _+K_
  infixr 55 -K_
  infixr 56 _-K_

  {- Proof that S¹→K2 is isomorphic to K2×K1 (as types). Needed for H²(T²)  -}
  S1→K2≡K2×K1' : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
  Iso.fun S1→K2≡K2×K1' f = f base , ΩKn+1→Kn 1 (sym (P.cancelK 2 (f base))
                                             ∙∙ cong (λ x → (f x) -K f base) loop
                                             ∙∙ P.cancelK 2 (f base))
  Iso.inv S1→K2≡K2×K1' = invmap
    where
    invmap : (∥ Susp S¹ ∥ 4) × (∥ S¹ ∥ 3) → S¹ → ∥ Susp S¹ ∥ 4
    invmap (a , b) base = a +K 0₂
    invmap (a , b) (loop i) = a +K Kn→ΩKn+1 1 b i
  Iso.rightInv S1→K2≡K2×K1' (a , b) = ΣPathP ((P.rUnitK 2 a)
                                           , (cong (ΩKn+1→Kn 1) (doubleCompPath-elim' (sym (P.cancelK 2 (a +K 0₂)))
                                             (λ i → (a +K Kn→ΩKn+1 1 b i) -K (a +K 0₂))
                                             (P.cancelK 2 (a +K 0₂)))
                                          ∙∙ cong (ΩKn+1→Kn 1) (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +K x) -K (a +K 0₂))
                                                               (funExt (λ x → sym (cancelHelper a x)))
                                                               (P.cancelK 2 (a +K 0₂)))
                                          ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 1) b))

      module _ where
      cancelHelper : (a b : coHomK 2) → (a +K b) -K (a +K 0₂) ≡ b
      cancelHelper a b = cong (λ x → (a +K b) -K x) (P.rUnitK 2 a)
                       ∙ P.-cancelLK 2 a b

      congHelper2 : (p : 0₂ ≡ 0₂) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) → (q : (f 0₂) ≡ 0₂)
                  → (sym q) ∙ cong f p ∙ q ≡ p
      congHelper2 p f = J (λ f _ → (q : (f 0₂) ≡ 0₂) → (sym q) ∙ cong f p ∙ q ≡ p)
                         λ q → (cong (sym q ∙_) (isCommΩK 2 p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
                              ∙ sym (lUnit p)

      conghelper3 : (x : coHomK 2) (p : x ≡ x) (f : coHomK 2 → coHomK 2) (id : (λ x → x) ≡ f) (q : f x ≡ x)
                  → (sym q) ∙ cong f p ∙ q ≡ p
      conghelper3 x p f = J (λ f _ → (q : (f x) ≡ x) → (sym q) ∙ cong f p ∙ q ≡ p)
                            λ q → (cong (sym q ∙_) (isCommΩK-based 2 x p _) ∙∙ assoc _ _ _ ∙∙ cong (_∙ p) (lCancel q))
                                      ∙  sym (lUnit p)
  Iso.leftInv S1→K2≡K2×K1' a = funExt λ { base → P.rUnitK _ (a base)
                                       ; (loop i) j → loopcase j i}
    where
    loopcase : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
                     (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.cancelK 2 (a base))
                           ∙∙ (λ i → a (loop i) -K (a (base)))
                           ∙∙ P.cancelK 2 (a base))))))
                     (cong a loop)
    loopcase i j = hcomp (λ k → λ { (i = i0) → a base +K Kn→ΩKn+1 1 (ΩKn+1→Kn 1 (doubleCompPath-elim'
                                                                                  (sym (P.cancelK 2 (a base)))
                                                                                  (λ i₁ → a (loop i₁) -K a base)
                                                                                  (P.cancelK 2 (a base)) (~ k))) j
                                  ; (i = i1) → cong a loop j
                                  ; (j = i0) → P.rUnitK 2 (a base) i
                                  ; (j = i1) → P.rUnitK 2 (a base) i})
                         (loopcase2 i j)

       where

       stupidAgda : (x : coHomK 2) (p : x ≡ x) (q : 0₂ ≡ x) → Kn→ΩKn+1 1 (ΩKn+1→Kn 1 (q ∙ p ∙ sym q)) ≡ q ∙ p ∙ sym q
       stupidAgda x p q = Iso.rightInv (Iso-Kn-ΩKn+1 1) (q ∙ p ∙ sym q)

       pathHelper : (a b : hLevelTrunc 4 (S₊ 2)) → a +K (b -K a) ≡ b
       pathHelper a b = P.commK 2 a (b -K a) ∙ P.-+cancelK 2 b a

       pathPHelper : PathP (λ i → pathHelper (a base) (a base) i ≡ pathHelper (a base) (a base) i)
                           (cong (a base +K_) (λ i₁ → a (loop i₁) -K a base))
                           λ i → a (loop i)
       pathPHelper i j = pathHelper (a base) (a (loop j)) i

       abstract
         helperFun2 : {A : Type₀} {0A a b : A} (main : 0A ≡ 0A) (start : b ≡ b) (p : a ≡ a) (q : a ≡ b) (r : b ≡ 0A) (Q : a ≡ 0A)
                      (R : PathP (λ i → Q i ≡ Q i) p main)
                      → start ≡ sym q ∙ p ∙ q
                      → isComm∙ (A , 0A)
                      → sym r ∙ start ∙ r ≡ main
         helperFun2 main start p q r Q R startId comm =
             sym r ∙ start ∙ r           ≡[ i ]⟨ sym r ∙ startId i ∙ r ⟩
             sym r ∙ (sym q ∙ p ∙ q) ∙ r ≡[ i ]⟨ sym r ∙ assoc (sym q) (p ∙ q) r (~ i) ⟩
             sym r ∙ sym q ∙ (p ∙ q) ∙ r ≡[ i ]⟨ sym r ∙ sym q ∙ assoc p q r (~ i) ⟩
             sym r ∙ sym q ∙ p ∙ q ∙ r ≡[ i ]⟨ assoc (sym r) (rUnit (sym q) i) (p ∙ lUnit (q ∙ r) i) i ⟩
             (sym r ∙ sym q ∙ refl) ∙ p ∙ refl ∙ q ∙ r ≡[ i ]⟨ (sym r ∙ sym q ∙ λ j → Q (i ∧ j)) ∙ R i ∙ (λ j → Q ( i ∧ (~ j))) ∙ q ∙ r ⟩
             (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ q ∙ r ≡[ i ]⟨ (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ symDistr (sym r) (sym q) (~ i) ⟩
             (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ sym (sym r ∙ sym q) ≡[ i ]⟨ (assoc (sym r) (sym q) Q i) ∙ main ∙ symDistr (sym r ∙ sym q) Q (~ i) ⟩
             ((sym r ∙ sym q) ∙ Q) ∙ main ∙ sym ((sym r ∙ sym q) ∙ Q)  ≡[ i ]⟨ ((sym r ∙ sym q) ∙ Q) ∙ comm main (sym ((sym r ∙ sym q) ∙ Q)) i ⟩
             ((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q) ∙ main ≡⟨ assoc ((sym r ∙ sym q) ∙ Q) (sym ((sym r ∙ sym q) ∙ Q)) main  ⟩
             (((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q)) ∙ main ≡[ i ]⟨ rCancel (((sym r ∙ sym q) ∙ Q)) i ∙ main ⟩
             refl ∙ main ≡⟨ sym (lUnit main) ⟩
             main ∎


       helper : cong (a base +K_)
                     (Kn→ΩKn+1 1
                       (ΩKn+1→Kn 1
                       (sym (P.cancelK 2 (a base))
                         ∙ (λ i₁ → a (loop i₁) -K a base)
                         ∙ P.cancelK 2 (a base))))
                   ≡ _
       helper = (λ i → cong (a base +K_) (stupidAgda (a base -K (a base))
                                                      (λ i₁ → a (loop i₁) -K a base)
                                                      (sym (P.cancelK 2 (a base))) i))
             ∙ congFunct₃ (a base +K_) (sym (P.cancelK 2 (a base)))
                                        (λ i₁ → a (loop i₁) -K a base)
                                        (P.cancelK 2 (a base))
         where
         congFunct₃ : ∀ {A B : Type₀} {a b c d : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
                    → cong f (p ∙ q ∙ r) ≡ cong f p ∙ cong f q ∙ cong f r
         congFunct₃ f p q r = congFunct f p (q ∙ r)
                            ∙ cong (cong f p ∙_) (congFunct f q r)

       loopcase2 : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
                     (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.cancelK 2 (a base))
                           ∙ (λ i → a (loop i) -K (a (base)))
                           ∙ P.cancelK 2 (a base))))))
                     (cong a loop)
       loopcase2 = compPathL→PathP (helperFun2 (cong a loop)
                                            _
                                            _
                                            (cong (a base +K_) (P.cancelK 2 (a base)))
                                            _
                                            _
                                            pathPHelper
                                            helper
                                            (isCommΩK-based 2 (a base)))


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
          (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _)
             λ fb gb → basechange-lemma base base (F ∘ ΩKn+1→Kn 1) (Kn→ΩKn+1 1 ∘ f) (Kn→ΩKn+1 1 ∘ g)
                                          (cong (Kn→ΩKn+1 1) fb ∙ Kn→ΩKn+10ₖ 1)
                                          (cong (Kn→ΩKn+1 1) gb ∙ Kn→ΩKn+10ₖ 1)
                       ∙ cong₂ (_∙_) (λ j i → basechange2⁻ (F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f base) j))
                                                            (cong (λ x → F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f x) j)) loop) i)
                                     λ j i → basechange2⁻ (F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g base) j))
                                                              (cong (λ x → F (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g x) j)) loop) i)

S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
S1→K2≡K2×K1 = S1→K2≡K2×K1' unlock
