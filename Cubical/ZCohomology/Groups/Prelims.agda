{-# OPTIONS --lossy-unification #-}
module Cubical.ZCohomology.Groups.Prelims where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +Comm to +ℤ-comm ; +Assoc to +ℤ-assoc)
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation as T
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure

infixr 33 _⋄_

_⋄_ : _
_⋄_ = compIso

-- We strengthen the elimination rule for Hⁿ(S¹). We show that we only need to work with elements ∣ f ∣₂ (definitionally) sending loop to some loop p
-- and sending base to 0
elimFunS¹ : (n : ℕ) → (p : typ (Ω (coHomK-ptd (suc n)))) → S¹ → coHomK (suc n)
elimFunS¹ n  p base = ∣ ptSn (suc n) ∣
elimFunS¹ n  p (loop i) = p i

coHomPointedElimS¹ : ∀ {ℓ} (n : ℕ) {B : coHom (suc n) S¹ → Type ℓ}
                 → ((x : coHom (suc n) S¹) → isProp (B x))
                 → ((p : typ (Ω (coHomK-ptd (suc n)))) → B ∣ elimFunS¹ n p ∣₂)
                 → (x : coHom (suc n) S¹) → B x
coHomPointedElimS¹ n {B = B} x p =
  coHomPointedElim n base x
    λ f Id → subst B
              (cong ∣_∣₂ (funExt (λ {base → sym Id ; (loop i) j → doubleCompPath-filler (sym Id) (cong f loop) Id (~ j) i})))
              (p (sym Id ∙∙ (cong f loop) ∙∙ Id))

coHomPointedElimS¹2 : ∀ {ℓ} (n : ℕ) {B : (x y : coHom (suc n) S¹) → Type ℓ}
                 → ((x y : coHom (suc n) S¹) → isProp (B x y))
                 → ((p q : typ (Ω (coHomK-ptd (suc n)))) → B ∣ elimFunS¹ n p ∣₂ ∣ elimFunS¹ n q ∣₂)
                 → (x y : coHom (suc n) S¹) → B x y
coHomPointedElimS¹2 n {B = B} x p =
  coHomPointedElim2 _ base x λ f g fId gId
    → subst2 B (cong ∣_∣₂ (funExt (λ {base → sym fId ; (loop i) j → doubleCompPath-filler (sym (fId)) (cong f loop) fId (~ j) i})))
                (cong ∣_∣₂ (funExt (λ {base → sym gId ; (loop i) j → doubleCompPath-filler (sym (gId)) (cong g loop) gId (~ j) i})))
                (p (sym fId ∙∙ cong f loop ∙∙ fId) (sym gId ∙∙ cong g loop ∙∙ gId))

-- We do the same thing for Sⁿ, n ≥ 2.
elimFunSⁿ : (n m : ℕ) (p : S₊ (suc m) → typ (Ω (coHomK-ptd (suc n))))
         → (S₊ (2 + m)) → coHomK (suc n)
elimFunSⁿ n m p north = ∣ ptSn (suc n) ∣
elimFunSⁿ n m p south = ∣ ptSn (suc n) ∣
elimFunSⁿ n m p (merid a i) = p a i

coHomPointedElimSⁿ : ∀ {ℓ} (n m : ℕ) {B : (x : coHom (suc n) (S₊ (2 + m))) → Type ℓ}
                 → ((x : coHom (suc n) (S₊ (2 + m))) → isProp (B x))
                 → ((p : _) → B ∣ elimFunSⁿ n m p ∣₂)
                 → (x : coHom (suc n) (S₊ (2 + m))) → B x
coHomPointedElimSⁿ n m {B = B} isprop ind =
  coHomPointedElim n north isprop
    λ f fId → subst B (cong ∣_∣₂ (funExt (λ {north → sym fId
                                           ; south → sym fId ∙' cong f (merid (ptSn (suc m)))
                                           ; (merid a i) j → hcomp (λ k → λ {(i = i0) → fId (~ j ∧ k)
                                                                             ; (i = i1) → compPath'-filler (sym fId)
                                                                                                            (cong f (merid (ptSn (suc m)))) k j
                                                                             ; (j = i1) → f (merid a i)})
                                                                    (hcomp (λ k → λ {(i = i0) → f north ;
                                                                                      (i = i1) → f (merid (ptSn (suc m)) (j ∨ ~ k)) ;
                                                                                      (j = i1) → f (merid a i)})
                                                                           (f (merid a i)))})))
                       (ind λ a → sym fId ∙∙ cong f (merid a) ∙ cong f (sym (merid (ptSn (suc m)))) ∙∙ fId)

0₀ = 0ₖ 0
0₁ = 0ₖ 1
0₂ = 0ₖ 2
0₃ = 0ₖ 3
0₄ = 0ₖ 4

S¹map : hLevelTrunc 3 S¹ → S¹
S¹map = T.rec isGroupoidS¹ (idfun _)

S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
S¹map-id = T.elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl


-- We prove that (S¹ → ∥ S¹ ∥) ≃ S¹ × ℤ (Needed for H¹(S¹)). Note that the truncation doesn't really matter, since S¹ is a groupoid.
-- Given a map f : S¹ → S¹, the idea is to send this to (f(base) , winding (f(loop))). For this to be
-- well-typed, we need to translate f(loop) into an element in Ω(S¹,base).

S¹→S¹≡S¹×ℤ : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × ℤ)
Iso.fun S¹→S¹≡S¹×ℤ f = S¹map (f base)
                 , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
Iso.inv S¹→S¹≡S¹×ℤ (s , int) base = ∣ s ∣
Iso.inv S¹→S¹≡S¹×ℤ (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
Iso.rightInv S¹→S¹≡S¹×ℤ (s , int) = ΣPathP (refl , ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                                      ∙ windingℤLoop int))
Iso.leftInv S¹→S¹≡S¹×ℤ f = funExt λ { base → S¹map-id (f base)
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
S1→K₁≡S1×ℤ : Iso ((S₊ 1) → coHomK 1) (coHomK 1 × ℤ)
S1→K₁≡S1×ℤ = S¹→S¹≡S¹×ℤ ⋄ prodIso (invIso (truncIdempotentIso 3 (isGroupoidS¹))) idIso

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
  Iso.fun S1→K2≡K2×K1' f = f base , ΩKn+1→Kn 1 (sym (P.rCancelK 2 (f base))
                                             ∙∙ cong (λ x → (f x) -K f base) loop
                                             ∙∙ P.rCancelK 2 (f base))
  Iso.inv S1→K2≡K2×K1' = invmap
    where
    invmap : (∥ Susp S¹ ∥ 4) × (∥ S¹ ∥ 3) → S¹ → ∥ Susp S¹ ∥ 4
    invmap (a , b) base = a +K 0₂
    invmap (a , b) (loop i) = a +K Kn→ΩKn+1 1 b i
  Iso.rightInv S1→K2≡K2×K1' (a , b) = ΣPathP ((P.rUnitK 2 a)
                                           , (cong (ΩKn+1→Kn 1) (doubleCompPath-elim' (sym (P.rCancelK 2 (a +K 0₂)))
                                             (λ i → (a +K Kn→ΩKn+1 1 b i) -K (a +K 0₂))
                                             (P.rCancelK 2 (a +K 0₂)))
                                          ∙∙ cong (ΩKn+1→Kn 1) (congHelper2 (Kn→ΩKn+1 1 b) (λ x → (a +K x) -K (a +K 0₂))
                                                               (funExt (λ x → sym (cancelHelper a x)))
                                                               (P.rCancelK 2 (a +K 0₂)))
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
  Iso.leftInv S1→K2≡K2×K1' a i base = P.rUnitK _ (a base) i
  Iso.leftInv S1→K2≡K2×K1' a i (loop j) = loop-helper i j
    where
    loop-helper : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
                     (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.rCancelK 2 (a base))
                           ∙∙ (λ i → a (loop i) -K (a (base)))
                           ∙∙ P.rCancelK 2 (a base))))))
                     (cong a loop)
    loop-helper i j =
      hcomp (λ k → λ { (i = i0) → (G (doubleCompPath-elim'
                                        (sym rP) (λ i₁ → a (loop i₁) -K a base) rP (~ k))) j
                      ; (i = i1) → cong a loop j
                      ; (j = i0) → P.rUnitK 2 (a base) i
                      ; (j = i1) → P.rUnitK 2 (a base) i})
             (loop-helper2 i j)

       where
       F : typ (Ω (coHomK-ptd 2)) → a base +K snd (coHomK-ptd 2) ≡ a base +K snd (coHomK-ptd 2)
       F = cong (_+K_ {n = 2} (a base))

       G : 0ₖ 2 ≡ 0ₖ 2 → a base +K snd (coHomK-ptd 2) ≡ a base +K snd (coHomK-ptd 2)
       G p = F (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 p))

       rP : P.+K 2 (a base) (P.-K 2 (a base)) ≡ 0ₖ 2
       rP = P.rCancelK 2 (a base)

       lem : (x : coHomK 2) (p : x ≡ x) (q : 0₂ ≡ x)
           → Kn→ΩKn+1 1 (ΩKn+1→Kn 1 (q ∙ p ∙ sym q)) ≡ q ∙ p ∙ sym q
       lem x p q = Iso.rightInv (Iso-Kn-ΩKn+1 1) (q ∙ p ∙ sym q)

       subtr-lem : (a b : hLevelTrunc 4 (S₊ 2)) → a +K (b -K a) ≡ b
       subtr-lem a b = P.commK 2 a (b -K a) ∙ P.-+cancelK 2 b a

       subtr-lem-coher : PathP (λ i → subtr-lem (a base) (a base) i ≡ subtr-lem (a base) (a base) i)
                           (cong (a base +K_) (λ i₁ → a (loop i₁) -K a base))
                           λ i → a (loop i)
       subtr-lem-coher i j = subtr-lem (a base) (a (loop j)) i

       abstract
         helperFun2 : {A : Type₀} {0A a b : A} (main : 0A ≡ 0A) (start : b ≡ b) (p : a ≡ a) (q : a ≡ b) (r : b ≡ 0A) (Q : a ≡ 0A)
                      (R : PathP (λ i → Q i ≡ Q i) p main)
                      → start ≡ sym q ∙ p ∙ q
                      → isComm∙ (A , 0A)
                      → sym r ∙ start ∙ r ≡ main
         helperFun2 main start p q r Q R startId comm =
             sym r ∙ start ∙ r                                            ≡[ i ]⟨ sym r ∙ startId i ∙ r ⟩
             sym r ∙ (sym q ∙ p ∙ q) ∙ r                                  ≡[ i ]⟨ sym r ∙ assoc (sym q) (p ∙ q) r (~ i) ⟩
             sym r ∙ sym q ∙ (p ∙ q) ∙ r                                  ≡[ i ]⟨ sym r ∙ sym q ∙ assoc p q r (~ i) ⟩
             sym r ∙ sym q ∙ p ∙ q ∙ r                                    ≡[ i ]⟨ assoc (sym r) (rUnit (sym q) i) (p ∙ lUnit (q ∙ r) i) i ⟩
             (sym r ∙ sym q ∙ refl) ∙ p ∙ refl ∙ q ∙ r                    ≡[ i ]⟨ (sym r ∙ sym q ∙ λ j → Q (i ∧ j)) ∙ R i ∙ (λ j → Q ( i ∧ (~ j))) ∙ q ∙ r ⟩
             (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ q ∙ r                   ≡[ i ]⟨ (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ symDistr (sym r) (sym q) (~ i) ⟩
             (sym r ∙ sym q ∙ Q) ∙ main ∙ sym Q ∙ sym (sym r ∙ sym q)     ≡[ i ]⟨ (assoc (sym r) (sym q) Q i) ∙ main ∙ symDistr (sym r ∙ sym q) Q (~ i) ⟩
             ((sym r ∙ sym q) ∙ Q) ∙ main ∙ sym ((sym r ∙ sym q) ∙ Q)     ≡[ i ]⟨ ((sym r ∙ sym q) ∙ Q) ∙ comm main (sym ((sym r ∙ sym q) ∙ Q)) i ⟩
             ((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q) ∙ main     ≡⟨ assoc ((sym r ∙ sym q) ∙ Q) (sym ((sym r ∙ sym q) ∙ Q)) main  ⟩
             (((sym r ∙ sym q) ∙ Q) ∙ sym ((sym r ∙ sym q) ∙ Q)) ∙ main   ≡[ i ]⟨ rCancel (((sym r ∙ sym q) ∙ Q)) i ∙ main ⟩
             refl ∙ main                                                  ≡⟨ sym (lUnit main) ⟩
             main ∎

         congFunct₃ : ∀ {A B : Type₀} {a b c d : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
                      → cong f (p ∙ q ∙ r) ≡ cong f p ∙ cong f q ∙ cong f r
         congFunct₃ f p q r = congFunct f p (q ∙ r) ∙ cong (cong f p ∙_) (congFunct f q r)

         lem₀ : G (sym rP ∙ (λ i₁ → a (loop i₁) -K a base) ∙ rP)
                 ≡ F (sym rP ∙ (λ i₁ → a (loop i₁) -K a base) ∙ rP)
         lem₀ = cong F (lem (a base -K (a base))
                               (λ i₁ → a (loop i₁) -K a base)
                               (sym (P.rCancelK 2 (a base))))

         lem₁ : G (sym rP ∙ (λ i₁ → a (loop i₁) -K a base) ∙ rP)
                ≡ sym (λ i₁ → a base +K P.rCancelK 2 (a base) i₁) ∙
                      cong (a base +K_) (λ i₁ → a (loop i₁) -K a base) ∙
                      (λ i₁ → a base +K P.rCancelK 2 (a base) i₁)
         lem₁ = lem₀ ∙ congFunct₃ (a base +K_) (sym rP)
                                                    (λ i₁ → a (loop i₁) -K a base)
                                                    rP

         loop-helper2 : PathP (λ i → P.rUnitK _ (a base) i ≡ P.rUnitK _ (a base) i)
                       (cong (a base +K_) (Kn→ΩKn+1 1 (ΩKn+1→Kn 1 ((sym (P.rCancelK 2 (a base))
                             ∙ (λ i → a (loop i) -K (a (base)))
                             ∙ P.rCancelK 2 (a base))))))
                       (cong a loop)
         loop-helper2 = compPathL→PathP (helperFun2 (cong a loop) _ _
                                                  (cong (a base +K_) (P.rCancelK 2 (a base))) _ _
                                                  subtr-lem-coher
                                                  lem₁
                                                  (isCommΩK-based 2 (a base)))

S1→K2≡K2×K1 : Iso (S₊ 1 → coHomK 2) (coHomK 2 × coHomK 1)
S1→K2≡K2×K1 = S1→K2≡K2×K1' unlock
