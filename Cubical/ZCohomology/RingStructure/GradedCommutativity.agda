{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.RingStructure.GradedCommutativity where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.Path

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Int
  renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +Comm to +ℤ-comm ; ·Comm to ∙-comm ; +Assoc to ℤ+-assoc ; -_ to -ℤ_)
  hiding (_+'_ ; +'≡+ ; isEven)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.Properties

private
  variable
    ℓ : Level

open PlusBis

natTranspLem : ∀ {ℓ} {A B : ℕ → Type ℓ} {n m : ℕ} (a : A n)
  (f : (n : ℕ) → (a : A n) → B n) (p : n ≡ m)
  → f m (subst A p a) ≡ subst B p (f n a)
natTranspLem {A = A} {B = B} a f p = sym (substCommSlice A B f p a)

transp0₁ : (n : ℕ) → subst coHomK (+'-comm 1 (suc n)) (0ₖ _) ≡ 0ₖ _
transp0₁ zero = refl
transp0₁ (suc n) = refl

transp0₂ : (n m : ℕ) → subst coHomK (+'-comm (suc (suc n)) (suc m)) (0ₖ _) ≡ 0ₖ _
transp0₂ n zero = refl
transp0₂ n (suc m) = refl

-- Recurring expressions
private
  ΩKn+1→Ω²Kn+2 : {k : ℕ} → typ (Ω (coHomK-ptd k)) → typ ((Ω^ 2) (coHomK-ptd (suc k)))
  ΩKn+1→Ω²Kn+2 x = sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _

  ΩKn+1→Ω²Kn+2' : {k : ℕ} → Kn→ΩKn+1 k (0ₖ k) ≡ Kn→ΩKn+1 k (0ₖ k) → typ ((Ω^ 2) (coHomK-ptd (suc k)))
  ΩKn+1→Ω²Kn+2' p = sym (Kn→ΩKn+10ₖ _) ∙∙ p ∙∙ Kn→ΩKn+10ₖ _

  Kn→Ω²Kn+2 : {k : ℕ} → coHomK k → typ ((Ω^ 2) (coHomK-ptd (2 + k)))
  Kn→Ω²Kn+2 x = ΩKn+1→Ω²Kn+2 (Kn→ΩKn+1 _ x)

-- Definition of of -ₖ'ⁿ̇*ᵐ
-- This definition is introduced to facilite the proofs
-ₖ'-helper : {k : ℕ} (n m : ℕ)
  → isEvenT n ⊎ isOddT n → isEvenT m ⊎ isOddT m
  → coHomKType k → coHomKType k
-ₖ'-helper {k = zero} n m (inl x₁) q x = x
-ₖ'-helper {k = zero} n m (inr x₁) (inl x₂) x = x
-ₖ'-helper {k = zero} n m (inr x₁) (inr x₂) x = 0 - x
-ₖ'-helper {k = suc zero} n m p q base = base
-ₖ'-helper {k = suc zero} n m (inl x) q (loop i) = loop i
-ₖ'-helper {k = suc zero} n m (inr x) (inl x₁) (loop i) = loop i
-ₖ'-helper {k = suc zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-ₖ'-helper {k = suc (suc k)} n m p q north = north
-ₖ'-helper {k = suc (suc k)} n m p q south = north
-ₖ'-helper {k = suc (suc k)} n m (inl x) q (merid a i) =
  (merid a ∙ sym (merid (ptSn (suc k)))) i
-ₖ'-helper {k = suc (suc k)} n m (inr x) (inl x₁) (merid a i) =
  (merid a ∙ sym (merid (ptSn (suc k)))) i
-ₖ'-helper {k = suc (suc k)} n m (inr x) (inr x₁) (merid a i) =
  (merid a ∙ sym (merid (ptSn (suc k)))) (~ i)

-ₖ'-gen : {k : ℕ} (n m : ℕ)
         (p : isEvenT n ⊎ isOddT n)
         (q : isEvenT m ⊎ isOddT m)
       → coHomK k → coHomK k
-ₖ'-gen {k = zero} = -ₖ'-helper {k = zero}
-ₖ'-gen {k = suc k} n m p q = T.map (-ₖ'-helper {k = suc k} n m p q)

-- -ₖ'ⁿ̇*ᵐ
-ₖ'^_·_ : {k : ℕ} (n m : ℕ) → coHomK k → coHomK k
-ₖ'^_·_ {k = k} n m = -ₖ'-gen n m (evenOrOdd n) (evenOrOdd m)

-- cohomology version
-ₕ'^_·_ : {k : ℕ} {A : Type ℓ} (n m : ℕ) → coHom k A → coHom k A
-ₕ'^_·_ n m = ST.map λ f x → (-ₖ'^ n · m) (f x)

-- -ₖ'ⁿ̇*ᵐ = -ₖ' for n m odd
-ₖ'-gen-inr≡-ₖ' : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ'-gen n m (inr p) (inr q) x ≡ (-ₖ x)
-ₖ'-gen-inr≡-ₖ' {k = zero} n m p q _ = refl
-ₖ'-gen-inr≡-ₖ' {k = suc zero} n m p q =
  T.elim ((λ _ → isOfHLevelTruncPath))
         λ { base → refl
          ; (loop i) → refl}
-ₖ'-gen-inr≡-ₖ' {k = suc (suc k)} n m p q =
  T.elim ((λ _ → isOfHLevelTruncPath))
         λ { north → refl
           ; south → refl
           ; (merid a i) k → ∣ symDistr (merid (ptSn _)) (sym (merid a)) (~ k) (~ i) ∣ₕ}

-- -ₖ'ⁿ̇*ᵐ x = x for n even
-ₖ'-gen-inl-left : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ'-gen n m (inl p) q x ≡ x
-ₖ'-gen-inl-left {k = zero} n m p q x = refl
-ₖ'-gen-inl-left {k = suc zero} n m p q =
  T.elim (λ _ → isOfHLevelTruncPath)
         λ { base → refl ; (loop i) → refl}
-ₖ'-gen-inl-left {k = suc (suc k)} n m p q =
  T.elim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i ∣ₕ}

-- -ₖ'ⁿ̇*ᵐ x = x for m even
-ₖ'-gen-inl-right : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ'-gen n m p (inl q) x ≡ x
-ₖ'-gen-inl-right {k = zero} n m (inl x₁) q x = refl
-ₖ'-gen-inl-right {k = zero} n m (inr x₁) q x = refl
-ₖ'-gen-inl-right {k = suc zero} n m (inl x₁) q =
  T.elim (λ _ → isOfHLevelTruncPath)
         λ { base → refl ; (loop i) → refl}
-ₖ'-gen-inl-right {k = suc zero} n m (inr x₁) q =
  T.elim (λ _ → isOfHLevelTruncPath)
         λ { base → refl ; (loop i) → refl}
-ₖ'-gen-inl-right {k = suc (suc k)} n m (inl x₁) q =
  T.elim (λ _ → isOfHLevelTruncPath)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}
-ₖ'-gen-inl-right {k = suc (suc k)} n m (inr x₁) q =
  T.elim (λ _ → isOfHLevelTruncPath)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}

-ₖ'-gen² : {k : ℕ} (n m : ℕ)
         (p : isEvenT n ⊎ isOddT n)
         (q : isEvenT m ⊎ isOddT m)
         → (x : coHomK k) → -ₖ'-gen n m p q (-ₖ'-gen n m p q x) ≡ x
-ₖ'-gen² {k = zero} n m (inl x₁) q x = refl
-ₖ'-gen² {k = zero} n m (inr x₁) (inl x₂) x = refl
-ₖ'-gen² {k = zero} n m (inr x₁) (inr x₂) x =
     cong (pos 0 -_) (-AntiComm (pos 0) x)
  ∙∙ -AntiComm (pos 0) (-ℤ (x - pos 0))
  ∙∙ h x
  where
  h : (x : _) →  -ℤ (-ℤ (x - pos 0) - pos 0) ≡ x
  h (pos zero) = refl
  h (pos (suc n)) = refl
  h (negsuc n) = refl
-ₖ'-gen² {k = suc k} n m (inl x₁) q x i =
  -ₖ'-gen-inl-left n m x₁ q (-ₖ'-gen-inl-left n m x₁ q x i) i
-ₖ'-gen² {k = suc k} n m (inr x₁) (inl x₂) x i =
  -ₖ'-gen-inl-right n m (inr x₁) x₂ (-ₖ'-gen-inl-right n m (inr x₁) x₂ x i) i
-ₖ'-gen² {k = suc k} n m (inr x₁) (inr x₂) x =
  (λ i → -ₖ'-gen-inr≡-ₖ' n m x₁ x₂ (-ₖ'-gen-inr≡-ₖ' n m x₁ x₂ x i) i) ∙ -ₖ^2 x

-ₖ'-genIso : {k : ℕ} (n m : ℕ)
         (p : isEvenT n ⊎ isOddT n)
         (q : isEvenT m ⊎ isOddT m)
       → Iso (coHomK k) (coHomK k)
Iso.fun (-ₖ'-genIso {k = k} n m p q) = -ₖ'-gen n m p q
Iso.inv (-ₖ'-genIso {k = k} n m p q) = -ₖ'-gen n m p q
Iso.rightInv (-ₖ'-genIso {k = k} n m p q) = -ₖ'-gen² n m p q
Iso.leftInv (-ₖ'-genIso {k = k} n m p q) = -ₖ'-gen² n m p q

-- action of cong on -ₖ'ⁿ̇*ᵐ
cong-ₖ'-gen-inr : {k : ℕ} (n m : ℕ)  (p : _) (q : _) (P : Path (coHomK (2 + k)) (0ₖ _) (0ₖ _))
     → cong (-ₖ'-gen n m (inr p) (inr q)) P ≡ sym P
cong-ₖ'-gen-inr {k = k} n m p q P = code≡sym (0ₖ _) P
  where
  code : (x : coHomK (2 + k)) → 0ₖ _ ≡ x → x ≡ 0ₖ _
  code = T.elim (λ _ → isOfHLevelΠ (4 + k) λ _ → isOfHLevelTruncPath)
                λ { north → cong (-ₖ'-gen n m (inr p) (inr q))
                  ; south P → cong ∣_∣ₕ (sym (merid (ptSn _))) ∙ (cong (-ₖ'-gen n m (inr p) (inr q)) P)
                  ; (merid a i) → t a i}
    where
    t : (a : S₊ (suc k)) → PathP (λ i → 0ₖ (2 + k) ≡ ∣ merid a i ∣ₕ → ∣ merid a i ∣ₕ ≡ 0ₖ (2 + k))
                                  (cong (-ₖ'-gen n m (inr p) (inr q)))
                                  (λ P → cong ∣_∣ₕ (sym (merid (ptSn _))) ∙ (cong (-ₖ'-gen n m (inr p) (inr q)) P))
    t a = toPathP (funExt λ P → cong (transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k))))
                   (cong (cong (-ₖ'-gen n m (inr p) (inr q))) (λ i → (transp (λ j → 0ₖ (suc (suc k)) ≡ ∣ merid a (~ j ∧ ~ i) ∣) i
                         (compPath-filler P (λ j → ∣ merid a (~ j) ∣ₕ) i))))
        ∙∙ cong (transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k)))) (congFunct (-ₖ'-gen n m (inr p) (inr q)) P (sym (cong ∣_∣ₕ (merid a))))
        ∙∙ (λ j → transp (λ i → ∣ merid a (i ∨ j) ∣ ≡ 0ₖ (suc (suc k))) j
                  (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                    (cong (-ₖ'-gen n m (inr p) (inr q)) P
                    ∙ cong (-ₖ'-gen n m (inr p) (inr q)) (sym (cong ∣_∣ₕ (merid a)))) j))
        ∙∙ (λ i → sym (cong ∣_∣ₕ (merid a))
                 ∙ isCommΩK (2 + k) (cong (-ₖ'-gen n m (inr p) (inr q)) P)
                                    (cong (-ₖ'-gen n m (inr p) (inr q)) (sym (cong ∣_∣ₕ (merid a)))) i)
        ∙∙ (λ j → (λ i → ∣ merid a (~ i ∨ j) ∣)
                 ∙ (cong ∣_∣ₕ (compPath-filler' (merid a) (sym (merid (ptSn _))) (~ j)) ∙ (λ i → -ₖ'-gen n m (inr p) (inr q) (P i))))
        ∙ sym (lUnit _))

  code≡sym : (x : coHomK (2 + k)) → (p : 0ₖ _ ≡ x) → code x p ≡ sym p
  code≡sym x = J (λ x p → code x p ≡ sym p) refl

cong-cong-ₖ'-gen-inr : {k : ℕ} (n m : ℕ) (p : _) (q : _)
    (P : Square (refl {x = 0ₖ (suc (suc k))}) refl refl refl)
  → cong (cong (-ₖ'-gen n m (inr p) (inr q))) P ≡ sym P
cong-cong-ₖ'-gen-inr n m p q P =
     rUnit _
  ∙∙ (λ k → (λ i → cong-ₖ'-gen-inr n m p q refl (i ∧ k))
          ∙∙ (λ i → cong-ₖ'-gen-inr n m p q (P i) k)
          ∙∙ λ i → cong-ₖ'-gen-inr n m p q refl (~ i ∧ k))
  ∙∙ (λ k → transportRefl refl k
          ∙∙ cong sym P
          ∙∙ transportRefl refl k)
  ∙∙ sym (rUnit (cong sym P))
  ∙∙ sym (sym≡cong-sym P)

Kn→ΩKn+1-ₖ'' : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → Kn→ΩKn+1 k (-ₖ'-gen n m (inr p) (inr q) x) ≡ sym (Kn→ΩKn+1 k x)
Kn→ΩKn+1-ₖ'' n m p q x = cong (Kn→ΩKn+1 _) (-ₖ'-gen-inr≡-ₖ' n m p q x) ∙ Kn→ΩKn+1-ₖ _ x

transpΩ² : {n m : ℕ} (p q : n ≡ m) → (P : _)
        → transport (λ i → refl {x = 0ₖ (p i)} ≡ refl {x = 0ₖ (p i)}) P
        ≡ transport (λ i → refl {x = 0ₖ (q i)} ≡ refl {x = 0ₖ (q i)}) P
transpΩ² p q P k = subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (isSetℕ _ _ p q k) P

-- Some technical lemmas about Kn→Ω²Kn+2 and its interaction with -ₖ'ⁿ̇*ᵐ and transports
-- TODO : Check if this can be cleaned up more by having more general lemmas
private
  lem₁ : (n : ℕ) (a : _)
    → (cong (cong (subst coHomK (+'-comm (suc zero) (suc (suc n)))))
          (Kn→Ω²Kn+2 ∣ a ∣ₕ))
     ≡ ΩKn+1→Ω²Kn+2
       (sym (transp0₁ n) ∙∙ cong (subst coHomK (+'-comm (suc zero) (suc n))) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ) ∙∙ transp0₁ n)
  lem₁ zero a =
       (λ k i j → transportRefl (Kn→Ω²Kn+2 ∣ a ∣ₕ i j) k)
     ∙ cong ΩKn+1→Ω²Kn+2 λ k → rUnit (λ i → transportRefl (Kn→ΩKn+1 1 ∣ a ∣ i) (~ k)) k
  lem₁ (suc n) a =
       (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ ~ k))}
                            ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ ~ k))}) (~ k)
                (λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc (suc n))) (i ∧ ~ k))) k
                (Kn→Ω²Kn+2 ∣ a ∣ₕ i j)))
    ∙∙ transpΩ² (+'-comm 1 (suc (suc (suc n))))
                (cong suc (+'-comm (suc zero) (suc (suc n))))
                (Kn→Ω²Kn+2 ∣ a ∣ₕ)
    ∙∙ sym (natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
             (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣)
              (λ _ → ΩKn+1→Ω²Kn+2)
              (+'-comm 1 (suc (suc n))))
    ∙∙ cong ΩKn+1→Ω²Kn+2
         (λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ k))
                              ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ k))) k
          (λ i → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ k))) (~ k)
           (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))
    ∙∙ cong ΩKn+1→Ω²Kn+2 (rUnit (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
                                   (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ)))

  lem₂ : (n : ℕ) (a : _) (p : _) (q : _)
    → (cong (cong (-ₖ'-gen (suc (suc n)) (suc zero) p q
                  ∘ (subst coHomK (+'-comm 1 (suc (suc n))))))
             (Kn→Ω²Kn+2 (∣ a ∣ₕ)))
     ≡ ΩKn+1→Ω²Kn+2
         (sym (transp0₁ n)
       ∙∙ cong (subst coHomK (+'-comm (suc zero) (suc n)))
                (cong (-ₖ'-gen (suc (suc n)) (suc zero) p q)
                 (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ))
       ∙∙ transp0₁ n)
  lem₂ n a (inl x) (inr y) =
       (λ k i j → (-ₖ'-gen-inl-left (suc (suc n)) 1 x (inr y) (
                    subst coHomK (+'-comm 1 (suc (suc n)))
                  (Kn→Ω²Kn+2 ∣ a ∣ₕ i j))) k)
    ∙∙ lem₁ n a
    ∙∙ cong ΩKn+1→Ω²Kn+2 (cong (sym (transp0₁ n) ∙∙_∙∙ transp0₁ n)
      λ k i → subst coHomK (+'-comm 1 (suc n))
              (-ₖ'-gen-inl-left (suc (suc n)) 1 x (inr y) (Kn→ΩKn+1 (suc n) ∣ a ∣ i) (~ k)))
  lem₂ n a (inr x) (inr y) =
       cong-cong-ₖ'-gen-inr (suc (suc n)) 1 x y
         (cong
        (cong
         (subst coHomK (+'-comm 1 (suc (suc n)))))
        (Kn→Ω²Kn+2 ∣ a ∣ₕ))
    ∙∙ cong sym (lem₁ n a)
    ∙∙ λ k → ΩKn+1→Ω²Kn+2
                (sym (transp0₁ n) ∙∙
                 cong (subst coHomK (+'-comm 1 (suc n)))
                 (cong-ₖ'-gen-inr (suc (suc n)) 1 x y
                  (Kn→ΩKn+1 (suc n) ∣ a ∣) (~ k))
                 ∙∙ transp0₁ n)

  lem₃ : (n m : ℕ) (q : _) (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n))) (x : _)
    → (((sym (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))
                                 ∙∙ (λ j → -ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                                (subst coHomK (+'-comm (suc (suc m)) (suc n)) (Kn→ΩKn+1 _ x j)))
                    ∙∙ cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))))
     ≡ (Kn→ΩKn+1 _ (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                      (subst coHomK (cong suc (+-comm (suc m) n)) x)))
  lem₃ n m q p x =
    sym (cong-∙∙ (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (sym (transp0₂ m n))
        (λ j → subst coHomK (+'-comm (suc (suc m)) (suc n)) (Kn→ΩKn+1 _ x j))
        (transp0₂ m n))
          ∙ h n m p q x
    where
    help : (n m : ℕ) (x : _)
      → ((sym (transp0₂ m n))
         ∙∙ (λ j → subst coHomK (+'-comm (suc (suc m)) (suc n))
                     (Kn→ΩKn+1 (suc (suc (m + n))) x j))
         ∙∙ transp0₂ m n)
         ≡ Kn→ΩKn+1 (suc (n + suc m))
                  (subst coHomK (cong suc (+-comm (suc m) n)) x)
    help zero m x =
         sym (rUnit _)
      ∙∙ (λ k i → transp (λ i → coHomK (+'-comm (suc (suc m)) 1 (i ∨ k))) k
            (Kn→ΩKn+1 _
              (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) 1 (i ∧ k)))) (~ k) x) i))
      ∙∙ cong (Kn→ΩKn+1 _)
           λ k → subst coHomK (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) 1))
                   (cong suc (+-comm (suc m) zero)) k) x
    help (suc n) m x =
      sym (rUnit _)
      ∙∙ ((λ k i → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ k))) k
            (Kn→ΩKn+1 _
             (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ k)))) (~ k) x) i)))
      ∙∙ cong (Kn→ΩKn+1 _)
          (λ k → subst coHomK (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                                            (cong suc (+-comm (suc m) (suc n))) k) x)

    h : (n m : ℕ) (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n))) (q : _) (x : _)
      →  cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
           (sym (transp0₂ m n)
            ∙∙ (λ j → subst coHomK (+'-comm (suc (suc m)) (suc n))
                       (Kn→ΩKn+1 (suc (suc (m + n))) x j))
            ∙∙ transp0₂ m n)
        ≡  Kn→ΩKn+1 (suc (n + suc m))
            (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
             (subst coHomK (cong suc (+-comm (suc m) n)) x))
    h n m (inl p) (inl q) x =
         (λ k → cong (-ₖ'-gen (suc n) (suc (suc m))
                  (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inr p) k) (inl q))
                    (help n m x k))
      ∙∙ ((λ k i → -ₖ'-gen-inl-right (suc n) (suc (suc m)) (inr p) q (help n m x i1 i) k))
      ∙∙ λ i → Kn→ΩKn+1 (suc (n + suc m))
                 (-ₖ'-gen-inl-right (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (inr p) (evenOrOdd (suc n)) i) q
                  (subst coHomK (cong suc (+-comm (suc m) n)) x) (~ i))
    h n m (inl p) (inr q) x =
       (λ k → cong (-ₖ'-gen (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inr p) k) (inr q))
           (help n m x k))
     ∙∙ cong-ₖ'-gen-inr (suc n) (suc (suc m)) p q (help n m x i1)
     ∙∙ sym (Kn→ΩKn+1-ₖ'' (suc n) (suc (suc m)) p q
          (subst coHomK (λ i → suc (+-comm (suc m) n i)) x))
      ∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
        (-ₖ'-gen (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (inr p) (evenOrOdd (suc n)) k) (inr q)
         (subst coHomK (cong suc (+-comm (suc m) n)) x))
    h n m (inr p) (inl q) x =
         (λ k → cong (-ₖ'-gen (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inl p) k) (inl q))
                   (help n m x k))
      ∙∙ (λ k i → -ₖ'-gen-inl-left (suc n) (suc (suc m)) p (inl q) (help n m x i1 i) k)
      ∙∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
                 (-ₖ'-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                  (subst coHomK (cong suc (+-comm (suc m) n)) x) (~ k))
    h n m (inr p) (inr q) x =
         (λ k → cong (-ₖ'-gen (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inl p) k) (inr q))
                    (help n m x k))
      ∙∙ (λ k i → -ₖ'-gen-inl-left (suc n) (suc (suc m)) p (inr q) (help n m x i1 i) k)
      ∙∙ cong (Kn→ΩKn+1 (suc (n + suc m)))
           (sym (-ₖ'-gen-inl-left (suc n) (suc (suc m)) p (inr q)
             (subst coHomK (λ i → suc (+-comm (suc m) n i)) x)))
       ∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
        (-ₖ'-gen (suc n) (suc (suc m)) (isPropEvenOrOdd (suc n) (inl p) (evenOrOdd (suc n)) k) (inr q)
         (subst coHomK (cong suc (+-comm (suc m) n)) x))

  lem₄ : (n m : ℕ) (q : _) (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n))) (a : _) (b : _)
          → cong (Kn→ΩKn+1 _) (((sym (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))
                                 ∙∙ (λ j → -ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                                (subst coHomK (+'-comm (suc (suc m)) (suc n))
                                  (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                    ∙∙ cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))))
           ≡ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                                               (subst coHomK (cong suc (+-comm (suc m) n))
                                               (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
  lem₄ n m q p a b = cong (cong (Kn→ΩKn+1 _)) (lem₃ n m q p (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))

  lem₅ : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
    → cong (cong (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                   ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
         (ΩKn+1→Ω²Kn+2 (sym (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m))
                     ∙∙ (λ i → -ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                   (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                     (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                     ∙∙ cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m)))
        ≡ Kn→Ω²Kn+2 (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                       (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                         (subst coHomK (cong suc (sym (+-suc n m))) (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ ∣ b ∣ₕ))))
  lem₅ n m p q a b =
       cong (cong (cong (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                        ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
            (cong (sym (Kn→ΩKn+10ₖ _) ∙∙_∙∙ Kn→ΩKn+10ₖ _)
              (lem₄ m n p q b a))
     ∙ help p q (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ ∣ b ∣)
    where
    annoying : (x : _)
      → cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
          (Kn→Ω²Kn+2 (subst coHomK (cong suc (+-comm (suc n) m)) x))
         ≡ Kn→Ω²Kn+2 (subst coHomK (cong suc (sym (+-suc n m))) x)
    annoying x =
        ((λ k → transp (λ i → refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) (i ∨  ~ k))}
                              ≡ refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) (i ∨ ~ k))}) (~ k)

                  λ i j → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ ~ k))) k
                    (Kn→Ω²Kn+2 (subst coHomK (cong suc (+-comm (suc n) m)) x) i j)))
      ∙∙ cong (transport (λ i → refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) i)}
                              ≡ refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) i)}))
              (natTranspLem {A = coHomK} x (λ _ → Kn→Ω²Kn+2) (cong suc (+-comm (suc n) m)))
      ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
             (cong (suc ∘ suc ∘ suc) (+-comm (suc n) m)) (+'-comm (suc (suc m)) (suc (suc n)))
             (Kn→Ω²Kn+2 x))
      ∙∙ (λ k → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
                       (isSetℕ _ _
                         (cong (suc ∘ suc ∘ suc) (+-comm (suc n) m) ∙ (+'-comm (suc (suc m)) (suc (suc n))))
                         (cong (suc ∘ suc ∘ suc) (sym (+-suc n m))) k)
                 (Kn→Ω²Kn+2 x))
      ∙∙ sym (natTranspLem {A = coHomK} x (λ _ → Kn→Ω²Kn+2) (cong suc (sym (+-suc n m))))

    help : (p : _) (q : _) (x : _) →
      cong (cong (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                ∘ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
           (Kn→Ω²Kn+2 (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                (subst coHomK (cong suc (+-comm (suc n) m)) x)))
        ≡ Kn→Ω²Kn+2
             (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
              (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
               (subst coHomK (cong suc (sym (+-suc n m))) x)))
    help (inl x) (inl y) z =
         (λ k i j →
           -ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
             (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
               ((ΩKn+1→Ω²Kn+2
                 (Kn→ΩKn+1 _ (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
                  (subst coHomK (cong suc (+-comm (suc n) m)) z) k))) i j)) k)
      ∙∙ annoying z
      ∙∙ cong Kn→Ω²Kn+2
          λ k → (-ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
                   (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
                    (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k)) (~ k))
    help (inl x) (inr y) z =
         (λ k i j →
           -ₖ'-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
            (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
              (Kn→Ω²Kn+2 (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
                           (subst coHomK (cong suc (+-comm (suc n) m)) z) k) i j)) k)
      ∙∙ annoying z
      ∙∙ cong Kn→Ω²Kn+2
               (λ k → (-ₖ'-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
                 (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
                  (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k)) (~ k)))
    help (inr x) (inl y) z =
         (λ k i j → -ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                        (Kn→Ω²Kn+2
                          (-ₖ'-gen (suc m) (suc (suc n)) (isPropEvenOrOdd (suc m) (evenOrOdd (suc m)) (inr y) k) (inr x)
                             (subst coHomK (cong suc (+-comm (suc n) m)) z)) i j)) k)
      ∙∙ cong (cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))) ∘  ΩKn+1→Ω²Kn+2)
            (Kn→ΩKn+1-ₖ'' (suc m) (suc (suc n)) y x
                     (subst coHomK (cong suc (+-comm (suc n) m)) z))
      ∙∙ cong sym (annoying z)
      ∙∙ cong ΩKn+1→Ω²Kn+2 (sym (Kn→ΩKn+1-ₖ'' (suc m) (suc (suc n)) y x
                             (subst coHomK (cong suc (sym (+-suc n m))) z)))
      ∙∙ cong Kn→Ω²Kn+2 λ k → (-ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
                                  (-ₖ'-gen (suc m) (suc (suc n)) (isPropEvenOrOdd (suc m) (evenOrOdd (suc m)) (inr y) (~ k)) (inr x)
                                   (subst coHomK (cong suc (sym (+-suc n m))) z)) (~ k))
    help (inr x) (inr y) z =
         (λ k → cong-cong-ₖ'-gen-inr (suc (suc n)) (suc (suc m)) x y
                  (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                     (Kn→Ω²Kn+2
                       (-ₖ'-gen (suc m) (suc (suc n))
                         (isPropEvenOrOdd (suc m) (evenOrOdd (suc m)) (inl y) k) (inr x)
                          (subst coHomK (cong suc (+-comm (suc n) m)) z)) i j)) k)
      ∙∙ cong (sym ∘ cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))) ∘  Kn→Ω²Kn+2)
               (-ₖ'-gen-inl-left (suc m) (suc (suc n)) y (inr x)
                (subst coHomK (cong suc (+-comm (suc n) m)) z))
      ∙∙ cong sym (annoying z)
      ∙∙ cong (sym ∘ Kn→Ω²Kn+2)
                (sym (-ₖ'-gen-inl-left (suc m) (suc (suc n)) y (inr x)
                      (subst coHomK (cong suc (sym (+-suc n m))) z)))
      ∙∙ cong ΩKn+1→Ω²Kn+2
              λ k → (Kn→ΩKn+1-ₖ'' (suc (suc n)) (suc (suc m)) x y
                      (-ₖ'-gen (suc m) (suc (suc n)) (
                         isPropEvenOrOdd (suc m) (evenOrOdd (suc m)) (inl y) (~ k)) (inr x)
                       (subst coHomK (cong suc (sym (+-suc n m))) z))) (~ k)

  lem₆ : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
    → flipSquare
        (Kn→Ω²Kn+2 (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                     (subst coHomK (cong suc (+-comm (suc m) n))
                     (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
       ≡ Kn→Ω²Kn+2
         (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
           (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
             (subst coHomK (cong suc (sym (+-suc n m)))
               (-ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                 (subst coHomK (+'-comm (suc m) (suc n)) (∣ b ∣ₕ ⌣ₖ ∣ a ∣ₕ))))))
  lem₆ n m p q a b =
      sym (sym≡flipSquare (Kn→Ω²Kn+2 (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                     (subst coHomK (cong suc (+-comm (suc m) n))
                     (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣)))))
     ∙ cong ΩKn+1→Ω²Kn+2
           (help₁
             (subst coHomK (cong suc (+-comm (suc m) n))
               (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ ∣ a ∣)) p q
          ∙ cong (Kn→ΩKn+1 _) (sym (help₂ (∣ b ∣ ⌣ₖ ∣ a ∣))))
    where
    help₁ : (x : _) (p : _) (q : _)
      → sym (Kn→ΩKn+1 (suc (n + suc m)) (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q x))
       ≡ Kn→ΩKn+1 (suc (n + suc m)) ((-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
          (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
           (-ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)) x))))
    help₁ z (inl x) (inl y) =
         cong (λ x → sym (Kn→ΩKn+1 (suc (n + suc m)) x))
           (-ₖ'-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd (suc n)) y z)
      ∙∙ sym (Kn→ΩKn+1-ₖ'' (suc n) (suc m) x y z)
      ∙∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
        (-ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
         (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
          (-ₖ'-gen (suc n) (suc m)
            (isPropEvenOrOdd (suc n) (inr x) (evenOrOdd (suc n)) k)
            (isPropEvenOrOdd (suc m) (inr y) (evenOrOdd (suc m)) k) z) (~ k)) (~ k))
    help₁ z (inl x) (inr y) =
         (λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                      (-ₖ'-gen (suc n) (suc (suc m))
                        (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inr x) k) (inr y) z)))
      ∙∙ cong sym (Kn→ΩKn+1-ₖ'' (suc n) (suc (suc m)) x y z)
      ∙∙ cong (Kn→ΩKn+1 (suc (n + suc m))) (sym (-ₖ'-gen-inl-right (suc n) (suc m) (inr x) y z))
       ∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
        (-ₖ'-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
         (-ₖ'-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
          (-ₖ'-gen (suc n) (suc m)
            (isPropEvenOrOdd (suc n) (inr x) (evenOrOdd (suc n)) k)
            (isPropEvenOrOdd (suc m) (inl y) (evenOrOdd (suc m)) k) z) (~ k)) (~ k))
    help₁ z (inr x) (inl y) =
         cong (λ x → sym (Kn→ΩKn+1 (suc (n + suc m)) x))
           (-ₖ'-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd (suc n)) y z)
      ∙∙ (λ k → Kn→ΩKn+1-ₖ'' (suc m) (suc (suc n)) y x
                  (-ₖ'-gen-inl-left (suc n) (suc m) x (inr y) z (~ k)) (~ k))
      ∙∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
                 (-ₖ'-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
                  (-ₖ'-gen (suc m) (suc (suc n))
                    (isPropEvenOrOdd (suc m) (inr y) (evenOrOdd (suc m)) k) (inr x)
                   (-ₖ'-gen (suc n) (suc m)
                     (isPropEvenOrOdd (suc n) (inl x) (evenOrOdd (suc n)) k)
                     (isPropEvenOrOdd (suc m) (inr y) (evenOrOdd (suc m)) k) z)) (~ k))
    help₁ z (inr x) (inr y) =
         ((λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                      (-ₖ'-gen (suc n) (suc (suc m))
                        (isPropEvenOrOdd (suc n) (evenOrOdd (suc n)) (inl x) k) (inr y) z))))
      ∙∙ cong sym (cong (Kn→ΩKn+1 (suc (n + suc m))) (-ₖ'-gen-inl-left (suc n) (suc (suc m)) x (inr y) z))
      ∙∙ (λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                     (-ₖ'-gen-inl-left (suc m) (suc (suc n)) y (inr x)
                       (-ₖ'-gen-inl-right (suc n) (suc m) (inl x) y z (~ k)) (~ k))))
       ∙ λ k → Kn→ΩKn+1-ₖ'' (suc (suc n)) (suc (suc m)) x y
                  (-ₖ'-gen (suc m) (suc (suc n)) (isPropEvenOrOdd (suc m) (inl y) (evenOrOdd (suc m)) k) (inr x)
                   (-ₖ'-gen (suc n) (suc m)
                     (isPropEvenOrOdd (suc n) (inl x) (evenOrOdd (suc n)) k)
                     (isPropEvenOrOdd (suc m) (inl y) (evenOrOdd (suc m)) k)  z)) (~ k)

    help₂ : (x : _) →
       (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
         (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
           (subst coHomK (cong suc (sym (+-suc n m)))
             (-ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
               (subst coHomK (+'-comm (suc m) (suc n)) x)))))
     ≡ -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
        (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
          (-ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
            (subst coHomK (cong suc (+-comm (suc m) n)) x)))
    help₂ x =
         (λ k → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                  (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                    (transp (λ i → coHomK ((cong suc (sym (+-suc n m))) (i ∨ k))) k
                     (-ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                       (transp (λ i → coHomK ((cong suc (sym (+-suc n m))) (i ∧ k))) (~ k)
                         (subst coHomK (+'-comm (suc m) (suc n)) x))))))
       ∙ cong (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                 ∘ -ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                 ∘ -ₖ'-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)))
              (sym (substComposite coHomK (+'-comm (suc m) (suc n)) ((cong suc (sym (+-suc n m)))) x)
              ∙ λ k → subst coHomK (isSetℕ _ _ (+'-comm (suc m) (suc n) ∙ cong suc (sym (+-suc n m)))
                        ((cong suc (+-comm (suc m) n))) k) x)

  lem₇ : (n : ℕ) (a : _) (p : _) (q : _)
    → ((λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt)
                          (transp0₁ n (~ i))))
    ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt)
                              (subst coHomK (+'-comm (suc zero) (suc n)) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i))) j)
    ∙∙ (λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt)
                          (transp0₁ n i))))
       ≡ (cong (Kn→ΩKn+1 (suc (suc (n + zero))))
           (sym (transp0₁ n)
         ∙∙ sym (cong (subst coHomK (+'-comm (suc zero) (suc n)))
                 (cong (-ₖ'-gen (suc (suc n)) (suc zero) p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)))
         ∙∙ transp0₁ n))
  lem₇ zero a (inl x) (inr tt) =
      (λ k → rUnit ((cong (Kn→ΩKn+1 _) (cong-ₖ'-gen-inr (suc zero) (suc zero) tt tt
                      (λ i → (subst coHomK (+'-comm (suc zero) (suc zero))
                       (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ i))) k))) (~ k))
    ∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc zero)))
               (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc zero))
                 (-ₖ'-gen-inl-left (suc (suc zero)) (suc zero) tt (inr tt)
                  (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ (~ i)) (~ k))) k)))
  lem₇ (suc n) a (inl x) (inr tt) =
      ((λ k → rUnit (cong (Kn→ΩKn+1 _)
        (λ i → -ₖ'-gen (suc (suc n)) (suc zero)
                 (isPropEvenOrOdd n (evenOrOdd (suc (suc n))) (inr x) k) (inr tt)
                   (subst coHomK (+'-comm (suc zero) (suc (suc n)))
                    (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)))) (~ k)))
    ∙∙ (((λ k → ((cong (Kn→ΩKn+1 _) (cong-ₖ'-gen-inr (suc (suc n)) (suc zero) x tt
           (λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n)))
                     (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) k))))))
    ∙∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc (suc n + zero))))
               (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc (suc n)))
                 (-ₖ'-gen-inl-left (suc (suc (suc n))) (suc zero) x (inr tt)
                   (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ (~ i)) (~ k))) k)))
  lem₇ (suc n) a (inr x) (inr tt) =
       (λ k → rUnit (λ i j → Kn→ΩKn+1 _
                  (-ₖ'-gen (suc (suc n)) (suc zero)
                          (isPropEvenOrOdd (suc (suc n)) (evenOrOdd (suc (suc n))) (inl x) k) (inr tt)
                     (subst coHomK (+'-comm (suc zero) (suc (suc n)))
                       (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) j) (~ k))
    ∙∙ (λ k i j → Kn→ΩKn+1 _ (-ₖ'-gen-inl-left (suc (suc n)) (suc zero) x (inr tt)
                                (subst coHomK (+'-comm (suc zero) (suc (suc n)))
                                  (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)) k) j)
    ∙∙ λ k → cong (Kn→ΩKn+1 _)
              (rUnit (sym (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
                (cong-ₖ'-gen-inr (suc (suc (suc n))) (suc zero) x tt (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ) (~ k)))) k)

-- ∣ a ∣ ⌣ₖ ∣ b ∣ ≡ -ₖ'ⁿ*ᵐ (∣ b ∣ ⌣ₖ ∣ a ∣) for n ≥ 1, m = 1
gradedComm'-elimCase-left : (n : ℕ) (p : _) (q : _) (a : S₊ (suc n)) (b : S¹) →
      (_⌣ₖ_  {n = suc n} {m = (suc zero)} ∣ a ∣ₕ ∣ b ∣ₕ)
    ≡ (-ₖ'-gen (suc n) (suc zero) p q)
       (subst coHomK (+'-comm (suc zero) (suc n))
        (_⌣ₖ_  {n = suc zero} {m = suc n} ∣ b ∣ₕ ∣ a ∣ₕ))
gradedComm'-elimCase-left zero (inr tt) (inr tt) a b =
    proof a b
  ∙ cong (-ₖ'-gen 1 1 (inr tt) (inr tt))
         (sym (transportRefl ((_⌣ₖ_ {n = suc zero} {m = suc zero} ∣ b ∣ ∣ a ∣))))
  where
  help : flipSquare (ΩKn+1→Ω²Kn+2' (λ j i → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop i ∣ₕ ∣ loop j ∣ₕ)) ≡
                    cong (cong (-ₖ'-gen 1 1 (inr tt) (inr tt)))
                      (ΩKn+1→Ω²Kn+2' (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ))
  help = sym (sym≡flipSquare _)
       ∙ sym (cong-cong-ₖ'-gen-inr 1 1 tt tt
              (ΩKn+1→Ω²Kn+2' (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ ∣ loop i ∣)))

  proof : (a b : S¹) → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ a ∣ₕ ∣ b ∣ₕ ≡
      -ₖ'-gen 1 1 (inr tt) (inr tt) (_⌣ₖ_ {n = suc zero} {m = suc zero} ∣ b ∣ ∣ a ∣)
  proof base base = refl
  proof base (loop i) k = -ₖ'-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k) i)
  proof (loop i) base k = Kn→ΩKn+10ₖ _ k i
  proof (loop i) (loop j) k =
    hcomp (λ r →  λ { (i = i0) → -ₖ'-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j)
                     ; (i = i1) → -ₖ'-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j)
                     ; (j = i0) → Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                     ; (j = i1) → Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                     ; (k = i0) → doubleCompPath-filler
                                    (sym (Kn→ΩKn+10ₖ _))
                                    (λ j i → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop i ∣ₕ ∣ loop j ∣ₕ)
                                    (Kn→ΩKn+10ₖ _) (~ r) j i
                     ; (k = i1) → (-ₖ'-gen 1 1 (inr tt) (inr tt)
                                    (doubleCompPath-filler
                                     (sym (Kn→ΩKn+10ₖ _))
                                     (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ)
                                     (Kn→ΩKn+10ₖ _) (~ r) i j))})
          (help k i j)
gradedComm'-elimCase-left (suc n) p q north b =
  cong (-ₖ'-gen (suc (suc n)) 1 p q ∘
            (subst coHomK (+'-comm 1 (suc (suc n)))))
              (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ b ∣ₕ))
gradedComm'-elimCase-left (suc n) p q south b =
  cong (-ₖ'-gen (suc (suc n)) 1 p q ∘
            (subst coHomK (+'-comm 1 (suc (suc n)))))
              ((sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ b ∣ₕ)) ∙ λ i → ∣ b ∣ ⌣ₖ ∣ merid (ptSn (suc n)) i ∣ₕ)
gradedComm'-elimCase-left (suc n) p q (merid a i) base k =
  hcomp (λ j → λ {(i = i0) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (0ₖ _)
                 ; (i = i1) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (compPath-filler (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ base ∣ₕ))
                                                     (λ i → ∣ base ∣ ⌣ₖ ∣ merid a i ∣ₕ) j k)
                 ; (k = i0) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ₕ ∣ base ∣ₕ
                 ; (k = i1) → -ₖ'-gen (suc (suc n)) 1 p q
                                (subst coHomK (+'-comm 1 (suc (suc n)))
                                 (∣ base ∣ₕ ⌣ₖ ∣ merid a i ∣ₕ))})
        (hcomp (λ j → λ {(i = i0) → ∣ north ∣
                        ; (i = i1) → ∣ north ∣
                        ; (k = i0) → (sym (Kn→ΩKn+10ₖ _)
                                    ∙ (λ j → Kn→ΩKn+1 _
                                         (sym (gradedComm'-elimCase-left n (evenOrOdd (suc n)) (inr tt) a base
                                        ∙ cong (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)) (transp0₁ n)) j))) j i
                        ; (k = i1) → ∣ north ∣})
               ∣ north ∣)
gradedComm'-elimCase-left (suc n) p q (merid a i) (loop j) k =
  hcomp (λ r →
    λ { (i = i0) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                      (subst coHomK (+'-comm 1 (suc (suc n)))))
                        (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ (loop j) ∣ₕ) k)
      ; (i = i1) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                      (subst coHomK (+'-comm 1 (suc (suc n)))))
                        (compPath-filler (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ (loop j) ∣ₕ))
                          (λ i → ∣ loop j ∣ ⌣ₖ ∣ merid (ptSn (suc n)) i ∣ₕ) r k)
      ; (k = i0) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ₕ ∣ loop j ∣ₕ
      ; (k = i1) → -ₖ'-gen (suc (suc n)) 1 p q
                     (subst coHomK (+'-comm 1 (suc (suc n)))
                      (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ
                        ∣ compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ r) i ∣ₕ))})
        (hcomp (λ r →
          λ { (i = i0) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                            (subst coHomK (+'-comm 1 (suc (suc n)))))
                              ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∧ r) j ∣
            ; (i = i1) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                            (subst coHomK (+'-comm 1 (suc (suc n)))))
                              ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∧ r) j ∣
            ; (k = i0) → help₂ r i j
            ; (k = i1) → -ₖ'-gen (suc (suc n)) 1 p q
                           (subst coHomK (+'-comm 1 (suc (suc n)))
                            (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ
                              (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))})
   (-ₖ'-gen (suc (suc n)) 1 p q
                           (subst coHomK (+'-comm 1 (suc (suc n)))
                            (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ
                              (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))))
    where
    P : Path _ (Kn→ΩKn+1 (suc (suc (n + 0))) (0ₖ _))
               (Kn→ΩKn+1 (suc (suc (n + 0))) (_⌣ₖ_ {n = (suc n)} {m = suc zero} ∣ a ∣ ∣ base ∣))
    P i = Kn→ΩKn+1 (suc (suc (n + 0)))
            ((sym (gradedComm'-elimCase-left n (evenOrOdd (suc n)) (inr tt) a base
              ∙ cong (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)) (transp0₁ n)) i))

    help₁ : (P ∙∙ ((λ i j → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a j ∣ₕ ∣ loop i ∣ₕ)) ∙∙ sym P)
         ≡ ((λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                   (transp0₁ n (~ i))))
        ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                  (subst coHomK (+'-comm 1 (suc n)) (∣ loop i ∣ₕ ⌣ₖ ∣ a ∣ₕ))) j)
        ∙∙ (λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                   (transp0₁ n i))))
    help₁ k i j =
        ((λ i → (Kn→ΩKn+1 (suc (suc (n + 0))))
                  (compPath-filler'
                    ((gradedComm'-elimCase-left n (evenOrOdd (suc n)) (inr tt) a base))
                   (cong (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                    (transp0₁ n)) (~ k) (~ i)))
       ∙∙ (λ i j → (Kn→ΩKn+1 _
                     (gradedComm'-elimCase-left n (evenOrOdd (suc n)) (inr tt) a (loop i) k) j))
       ∙∙ λ i → (Kn→ΩKn+1 (suc (suc (n + 0))))
                   (compPath-filler'
                     ((gradedComm'-elimCase-left n (evenOrOdd (suc n)) (inr tt) a base))
                    (cong (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                     (transp0₁ n)) (~ k) i)) i j

    help₂ : I → I → I → coHomK _
    help₂ r i j =
      hcomp (λ k →
        λ { (i = i0) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                           subst coHomK (+'-comm 1 (suc (suc n))))
                          ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∨ r) j ∣
          ; (i = i1) → (-ₖ'-gen (suc (suc n)) 1 p q ∘
                           subst coHomK (+'-comm 1 (suc (suc n))))
                          ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∨ r) j ∣
          ; (j = i0) → compPath-filler (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))))
                          P k r i
          ; (j = i1) → compPath-filler (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))))
                          P k r i
          ; (r = i0) → -ₖ'-gen (suc (suc n)) 1 p q
                         (subst coHomK (+'-comm 1 (suc (suc n)))
                           (doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
                             (λ i j → _⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ
                                         (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i)) (Kn→ΩKn+10ₖ _) (~ k) i j))
          ; (r = i1) → doubleCompPath-filler P
                         (λ i j → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a j ∣ₕ ∣ loop i ∣ₕ)
                         (sym P) (~ k) j i})
             (hcomp (λ k →
               λ { (i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) (~ r) i
                 ; (j = i1) → (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) (~ r) i
                 ; (r = i0) → lem₂ n a p q (~ k) i j
                 ; (r = i1) → help₁ (~ k) j i})
                    (hcomp (λ k →
                      λ { (i = i0) → ∣ north ∣
                        ; (i = i1) → ∣ north ∣
                        ; (j = i0) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r) i
                        ; (j = i1) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r) i
                        ; (r = i0) → flipSquare≡cong-sym (flipSquare (ΩKn+1→Ω²Kn+2
                                                (sym (transp0₁ n)
                                              ∙∙ cong (subst coHomK (+'-comm 1 (suc n)))
                                                  (cong (-ₖ'-gen (suc (suc n)) 1 p q)
                                                   (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ))
                                              ∙∙ transp0₁ n))) (~ k) i j
                        ; (r = i1) → ((λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                                 (transp0₁ n (~ i))))
                                    ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                                  (subst coHomK (+'-comm 1 (suc n)) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i))) j)
                                    ∙∙ (λ i → Kn→ΩKn+1 _ (-ₖ'-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                                  (transp0₁ n i)))) j i})
                              (hcomp (λ k →
                                λ { (i = i0) → ∣ north ∣
                                  ; (i = i1) → ∣ north ∣
                                  ; (j = i0) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r ∧ k) i
                                  ; (j = i1) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r ∧ k) i
                                  ; (r = i0) → doubleCompPath-filler
                                                  (sym (Kn→ΩKn+10ₖ _))
                                                  (cong (Kn→ΩKn+1 (suc (suc (n + 0))))
                                                      (sym (transp0₁ n)
                                                    ∙∙ sym (cong (subst coHomK (+'-comm 1 (suc n)))
                                                             (cong (-ₖ'-gen (suc (suc n)) 1 p q)
                                                               (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)))
                                                    ∙∙ transp0₁ n))
                                                (Kn→ΩKn+10ₖ _) k j i
                                  ; (r = i1) → lem₇ n a p q (~ k) j i})
                                         (lem₇ n a p q i1 j i))))

-- ∣ a ∣ ⌣ₖ ∣ b ∣ ≡ -ₖ'ⁿ*ᵐ (∣ b ∣ ⌣ₖ ∣ a ∣) for all n, m ≥ 1
gradedComm'-elimCase : (k n m : ℕ) (term : n + m ≡ k) (p : _) (q : _) (a : _) (b : _) →
      (_⌣ₖ_  {n = suc n} {m = (suc m)} ∣ a ∣ₕ ∣ b ∣ₕ)
    ≡ (-ₖ'-gen (suc n) (suc m) p q)
       (subst coHomK (+'-comm (suc m) (suc n))
        (_⌣ₖ_  {n = suc m} {m = suc n} ∣ b ∣ₕ ∣ a ∣ₕ))
gradedComm'-elimCase k zero zero term p q a b = gradedComm'-elimCase-left zero p q a b
gradedComm'-elimCase k zero (suc m) term (inr tt) q a b =
    help q
  ∙ sym (cong (-ₖ'-gen 1 (suc (suc m)) (inr tt) q
             ∘ (subst coHomK (+'-comm (suc (suc m)) 1)))
        (gradedComm'-elimCase-left (suc m) q (inr tt) b a))
  where
  help : (q : _) → ∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ ≡
            -ₖ'-gen 1 (suc (suc m)) (inr tt) q
            (subst coHomK (+'-comm (suc (suc m)) 1)
             (-ₖ'-gen (suc (suc m)) 1 q (inr tt)
              (subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))))
  help (inl x) =
      (sym (transportRefl _)
     ∙ (λ i → subst coHomK (isSetℕ _ _ refl (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) i)
               (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)))
    ∙∙ substComposite coHomK
         (+'-comm 1 (suc (suc m)))
          (+'-comm (suc (suc m)) 1)
           ((∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))
    ∙∙ λ i → -ₖ'-gen-inl-right (suc zero) (suc (suc m)) (inr tt) x
            ((subst coHomK (+'-comm (suc (suc m)) 1)
             (-ₖ'-gen-inl-left (suc (suc m)) 1 x (inr tt)
              (subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)) (~ i)))) (~ i)
  help (inr x) =
       (sym (transportRefl _)
    ∙∙ (λ k → subst coHomK (isSetℕ _ _ refl (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) k) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))
    ∙∙ sym (-ₖ^2 (subst coHomK (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))))
    ∙∙ (λ i → -ₖ'-gen-inr≡-ₖ' 1 (suc (suc m)) tt x
                (-ₖ'-gen-inr≡-ₖ' (suc (suc m)) 1 x tt
                  (substComposite coHomK (+'-comm 1 (suc (suc m))) (+'-comm (suc (suc m)) 1) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ) i)
                  (~ i)) (~ i))
    ∙∙ λ i → (-ₖ'-gen 1 (suc (suc m)) (inr tt) (inr x)
                  (transp (λ j → coHomK ((+'-comm (suc (suc m)) 1) (j ∨ ~ i))) (~ i)
                    (-ₖ'-gen (suc (suc m)) 1 (inr x) (inr tt)
                      (transp (λ j → coHomK ((+'-comm (suc (suc m)) 1) (j ∧ ~ i))) i
                              ((subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)))))))
gradedComm'-elimCase k (suc n) zero term p q a b =
  gradedComm'-elimCase-left (suc n) p q a b
gradedComm'-elimCase zero (suc n) (suc m) term p q a b =
  ⊥.rec (snotz (sym (+-suc n m) ∙ cong predℕ term))
gradedComm'-elimCase (suc zero) (suc n) (suc m) term p q a b =
  ⊥.rec (snotz (sym (+-suc n m) ∙ cong predℕ term))
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q north north = refl
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q north south = refl
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q north (merid a i) r =
  -ₖ'-gen (suc (suc n)) (suc (suc m)) p q (
    (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
      ((sym (Kn→ΩKn+10ₖ _)
      ∙ cong (Kn→ΩKn+1 _)
          (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (transp0₂ n m))
                 ∙ sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
             (evenOrOdd (suc m)) p a north))) r i))
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q south north = refl
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q south south = refl
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q south (merid a i) r =
  -ₖ'-gen (suc (suc n)) (suc (suc m)) p q (
    (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
      ((sym (Kn→ΩKn+10ₖ _)
      ∙ cong (Kn→ΩKn+1 _)
          (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (transp0₂ n m))
                  ∙ sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
             (evenOrOdd (suc m)) p a south))) r i))
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q (merid a i) north r =
    (cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
      (gradedComm'-elimCase (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a north
       ∙ cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))
   ∙' Kn→ΩKn+10ₖ _) r i
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q (merid a i) south r =
    (cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
      (gradedComm'-elimCase (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a south
       ∙ cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n))
   ∙' Kn→ΩKn+10ₖ _) r i
gradedComm'-elimCase (suc (suc k)) (suc n) (suc m) term p q (merid a i) (merid b j) r =
  hcomp (λ l →
    λ { (i = i0) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q (
                     (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                       ((compPath-filler (sym (Kn→ΩKn+10ₖ _))
                        (cong (Kn→ΩKn+1 _)
                          (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (transp0₂ n m))
                                   ∙ sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                               (evenOrOdd (suc m)) p b north))) l r j)))
       ; (i = i1) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q (
                     (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                       ((compPath-filler (sym (Kn→ΩKn+10ₖ _))
                        (cong (Kn→ΩKn+1 _)
                          (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (transp0₂ n m))
                                  ∙ sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                              (evenOrOdd (suc m)) p b south))) l r j)))
       ; (r = i0) → help₂ l i j
       ; (r = i1) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                       (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                        (help₁ l i j))})
   (hcomp (λ l →
     λ { (i = i0) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                        (Kn→ΩKn+10ₖ _ (~ r ∨ ~ l) j))
       ; (i = i1) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                        (Kn→ΩKn+10ₖ _ (~ r ∨ ~ l) j))
       ; (j = i0) → Kn→ΩKn+10ₖ _ r i
       ; (j = i1) → Kn→ΩKn+10ₖ _ r i
       ; (r = i0) → lem₄ n m q p a b (~ l) j i
       ; (r = i1) → -ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                        (doubleCompPath-filler
                         (sym (Kn→ΩKn+10ₖ _))
                          (λ i j → Kn→ΩKn+1 _ ((sym (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m))
                                             ∙∙ (λ i → -ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                           (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                             (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                             ∙∙ cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m)) i) j)
                          (Kn→ΩKn+10ₖ _) (~ l) i j))})
        (hcomp (λ l →
          λ { (i = i0) → ∣ north ∣
            ; (i = i1) → ∣ north ∣
            ; (j = i0) → Kn→ΩKn+10ₖ _ r i
            ; (j = i1) → Kn→ΩKn+10ₖ _ r i
            ; (r = i0) → lem₄ n m q p a b i1 j i
            ; (r = i1) → lem₅ n m p q a b (~ l) i j})
            (hcomp (λ l →
              λ { (i = i0) → ∣ north ∣
                ; (i = i1) → ∣ north ∣
                ; (j = i0) → Kn→ΩKn+10ₖ _ (r ∨ ~ l) i
                ; (j = i1) → Kn→ΩKn+10ₖ _ (r ∨ ~ l) i
                ; (r = i0) → doubleCompPath-filler
                               (sym (Kn→ΩKn+10ₖ _))
                               (lem₄ n m q p a b i1)
                               (Kn→ΩKn+10ₖ _) (~ l) j i
                ; (r = i1) → Kn→Ω²Kn+2 (-ₖ'-gen (suc (suc n)) (suc (suc m)) p q
                                            (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                              (subst coHomK (cong suc (sym (+-suc n m)))
                                                (gradedComm'-elimCase k n m
                                                  (+-comm n m ∙∙ cong predℕ (+-comm (suc m) n) ∙∙ cong (predℕ ∘ predℕ) term)
                                                  (evenOrOdd (suc n)) (evenOrOdd (suc m)) a b (~ l))))) i j})
                (lem₆ n m p q a b r i j))))
  where
  help₁ : I → I → I → coHomK _
  help₁ l i j =
    Kn→ΩKn+1 _
      (hcomp (λ r
        → λ { (i = i0) → compPath-filler' (cong ((-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (transp0₂ n m)))
                            (sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                        (evenOrOdd (suc m)) p b north)) r l
              ; (i = i1) → compPath-filler' (cong ((-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (transp0₂ n m)))
                             (sym (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                        (evenOrOdd (suc m)) p b south)) r l
              ; (l = i0) → doubleCompPath-filler (sym (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m)))
                                                  (λ i → -ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                           (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                             (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                                  (cong (-ₖ'-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (transp0₂ n m)) r i
              ; (l = i1) → _⌣ₖ_ {n = suc m} {m = suc (suc n)} ∣ b ∣ₕ ∣ merid a i ∣ₕ})
          (gradedComm'-elimCase (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
            (evenOrOdd (suc m)) p b (merid a i) (~ l))) j

  help₂ : I → I → I → coHomK _
  help₂ l i j =
    hcomp (λ r →
      λ { (i = i0) → ∣ north ∣
         ; (i = i1) → ∣ north ∣
         ; (j = i0) →
           Kn→ΩKn+1 (suc (suc (n + suc m)))
                (compPath-filler (gradedComm'-elimCase (suc k) n (suc m)
                                  (cong predℕ term) (evenOrOdd (suc n)) q a north)
                  (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)  (transp0₂ m n)) r (~ l)) i
         ; (j = i1) →
              Kn→ΩKn+1 (suc (suc (n + suc m)))
                (compPath-filler (gradedComm'-elimCase (suc k) n (suc m)
                                 (cong predℕ term) (evenOrOdd (suc n)) q a south)
                  (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n)) r (~ l)) i
         ; (l = i0) →
           Kn→ΩKn+1 _
             (doubleCompPath-filler (sym (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n)))
                                    (λ j → -ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                                             (subst coHomK (+'-comm (suc (suc m)) (suc n))
                                               (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                                    (cong (-ₖ'-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (transp0₂ m n)) r j) i
         ; (l = i1) → Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc n)} {m = suc (suc m)} ∣ a ∣ ∣ merid b j ∣ₕ) i})
          (hcomp (λ r →
            λ { (i = i0) → ∣ north ∣
              ; (i = i1) → ∣ north ∣
              ; (j = i0) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                             (gradedComm'-elimCase (suc k) n (suc m)
                               (cong predℕ term) (evenOrOdd (suc n)) q a north (~ l ∨ ~ r)) i
              ; (j = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                             (gradedComm'-elimCase (suc k) n (suc m)
                               (cong predℕ term) (evenOrOdd (suc n)) q a south (~ l ∨ ~ r)) i
              ; (l = i0) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                             (gradedComm'-elimCase (suc k) n (suc m)
                               (cong predℕ term) (evenOrOdd (suc n)) q a (merid b j) i1) i
              ; (l = i1) → Kn→ΩKn+1 _ (gradedComm'-elimCase (suc k) n (suc m) (cong predℕ term)
                                          (evenOrOdd (suc n)) q a (merid b j) (~ r)) i})
               (Kn→ΩKn+1 (suc (suc (n + suc m)))
                 (gradedComm'-elimCase (suc k) n (suc m) (cong predℕ term)
                   (evenOrOdd (suc n)) q a (merid b j) i1) i))

private
  coherence-transp : (n m : ℕ) (p : _) (q : _)
   → -ₖ'-gen (suc n) (suc m) p q
        (subst coHomK (+'-comm (suc m) (suc n)) (0ₖ (suc m +' suc n))) ≡ 0ₖ _
  coherence-transp zero zero p q = refl
  coherence-transp zero (suc m) p q = refl
  coherence-transp (suc n) zero p q = refl
  coherence-transp (suc n) (suc m) p q = refl

gradedComm'-⌣ₖ∙ : (n m : ℕ) (p : _) (q : _) (a : _)
    → ⌣ₖ∙ (suc n) (suc m) a
  ≡ ((λ b → -ₖ'-gen (suc n) (suc m) p q (subst coHomK (+'-comm (suc m) (suc n)) (b ⌣ₖ a)))
    , (cong (-ₖ'-gen (suc n) (suc m) p q)
       (cong (subst coHomK (+'-comm (suc m) (suc n)))
        (0ₖ-⌣ₖ (suc m) (suc n) a))
   ∙ coherence-transp n m p q))
gradedComm'-⌣ₖ∙ n m p q =
  T.elim (λ _ → isOfHLevelPath (3 + n) ((isOfHLevel↑∙ (suc n) m)) _ _)
    λ a → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ b → funExt⁻ (cong fst (f₁≡f₂ b)) a)
  where
  f₁ : coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  fst (f₁ b) a = _⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ b
  snd (f₁ b) = 0ₖ-⌣ₖ (suc n) (suc m) b

  f₂ : coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  fst (f₂ b) a =
    -ₖ'-gen (suc n) (suc m) p q (subst coHomK (+'-comm (suc m) (suc n))
      (_⌣ₖ_ {n = suc m} {m = suc n} b ∣ a ∣ₕ))
  snd (f₂ b) =
    (cong (-ₖ'-gen (suc n) (suc m) p q)
            (cong (subst coHomK (+'-comm (suc m) (suc n)))
             (⌣ₖ-0ₖ (suc m) (suc n) b))
       ∙ coherence-transp n m p q)

  f₁≡f₂ : (b : _) → f₁ b ≡ f₂ b
  f₁≡f₂ =
    T.elim (λ _ → isOfHLevelPath (3 + m)
                    (subst (isOfHLevel (3 + m))
                     (λ i → S₊∙ (suc n) →∙ coHomK-ptd (+'-comm (suc n) (suc m) (~ i)))
                      (isOfHLevel↑∙' (suc m) n)) _ _)
     λ b → →∙Homogeneous≡ (isHomogeneousKn _)
             (funExt λ a → gradedComm'-elimCase (n + m) n m refl p q a b)

-- Finally, graded commutativity:
gradedComm'-⌣ₖ : (n m : ℕ) (a : coHomK n) (b : coHomK m)
  → a ⌣ₖ b ≡ (-ₖ'^ n · m) (subst coHomK (+'-comm m n) (b ⌣ₖ a))
gradedComm'-⌣ₖ zero zero a b = sym (transportRefl _) ∙ cong (transport refl) (comm-·₀ a b)
gradedComm'-⌣ₖ zero (suc m) a b =
      sym (transportRefl _)
  ∙∙ (λ k → subst coHomK (isSetℕ _ _ refl (+'-comm (suc m) zero) k) (b ⌣ₖ a))
  ∙∙ sym (-ₖ'-gen-inl-left zero (suc m) tt (evenOrOdd (suc m))
          (subst coHomK (+'-comm (suc m) zero) (b ⌣ₖ a)))
gradedComm'-⌣ₖ (suc n) zero a b =
     sym (transportRefl _)
  ∙∙ ((λ k → subst coHomK (isSetℕ _ _ refl (+'-comm zero (suc n)) k) (b ⌣ₖ a)))
  ∙∙ sym (-ₖ'-gen-inl-right (suc n) zero (evenOrOdd (suc n)) tt
          (subst coHomK (+'-comm zero (suc n)) (b ⌣ₖ a)))
gradedComm'-⌣ₖ (suc n) (suc m) a b =
  funExt⁻ (cong fst (gradedComm'-⌣ₖ∙ n m (evenOrOdd (suc n)) (evenOrOdd (suc m)) a)) b


gradedComm'-⌣ : {A : Type ℓ} (n m : ℕ) (a : coHom n A) (b : coHom m A)
  → a ⌣ b ≡ (-ₕ'^ n · m) (subst (λ n → coHom n A) (+'-comm m n) (b ⌣ a))
gradedComm'-⌣ n m =
  ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
    λ f g →
      cong ∣_∣₂ (funExt (λ x →
        gradedComm'-⌣ₖ n m (f x) (g x)
      ∙ cong ((-ₖ'^ n · m) ∘ (subst coHomK (+'-comm m n)))
         λ i → g (transportRefl x (~ i)) ⌣ₖ f (transportRefl x (~ i))))

-----------------------------------------------------------------------------
-- The previous code introduces another - to facilitate proof
-- This a reformulation with the usual -ₕ' definition (the one of the ring) of the results

-ₕ^-gen : {k : ℕ} → {A : Type ℓ} → (n m : ℕ)
         → (p : isEvenT n ⊎ isOddT n)
         → (q : isEvenT m ⊎ isOddT m)
         → (a : coHom k A) → coHom k A
-ₕ^-gen n m (inl p) q a       = a
-ₕ^-gen n m (inr p) (inl q) a = a
-ₕ^-gen n m (inr p) (inr q) a = -ₕ a

-ₕ^_·_ : {k : ℕ} → {A : Type ℓ} → (n m : ℕ) → (a : coHom k A) → coHom k A
-ₕ^_·_ n m a = -ₕ^-gen n m (evenOrOdd n) (evenOrOdd m) a

-ₕ^-gen-eq : ∀ {ℓ} {k : ℕ} {A : Type ℓ} (n m : ℕ)
  → (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
  → (x : coHom k A)
  → -ₕ^-gen n m p q x  ≡ (ST.map λ f x → (-ₖ'-gen n m p q) (f x)) x
-ₕ^-gen-eq {k = k} n m (inl p) q = ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂ (funExt λ x → sym (-ₖ'-gen-inl-left n m p q (f x)))
-ₕ^-gen-eq {k = k} n m (inr p) (inl q) = ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂ (funExt λ z → sym (-ₖ'-gen-inl-right n m (inr p) q (f z)))
-ₕ^-gen-eq {k = k} n m (inr p) (inr q) = ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂ (funExt λ z → sym (-ₖ'-gen-inr≡-ₖ' n m p q (f z)))

-ₕ^-eq : ∀ {ℓ} {k : ℕ} {A : Type ℓ} (n m : ℕ) → (a : coHom k A)
             → (-ₕ^ n · m) a  ≡ (-ₕ'^ n · m) a
-ₕ^-eq n m a = -ₕ^-gen-eq n m (evenOrOdd n) (evenOrOdd m) a

gradedComm-⌣ : ∀ {ℓ} {A : Type ℓ} (n m : ℕ) (a : coHom n A) (b : coHom m A)
  → a ⌣ b ≡ (-ₕ^ n · m) (subst (λ n → coHom n A) (+'-comm m n) (b ⌣ a))
gradedComm-⌣ n m a b = (gradedComm'-⌣ n m a b) ∙ (sym (-ₕ^-eq n m (subst (λ n₁ → coHom n₁ _) (+'-comm m n) (b ⌣ a))))


-----------------------------------------------------------------------------
-- Simplify -ₕ^

module _
  {ℓ : Level}
  {A : Type ℓ}
  (n : ℕ)
  (m : ℕ)
  where

  -ₕ^-EvenEven : (isEven n ≡ true) → (isEven m ≡ true) →
                 (x : coHom (m +' n) A) → (-ₕ^ n · m) x ≡ x
  -ₕ^-EvenEven p q x = cong₂ (λ X Y → -ₕ^-gen n m X Y x) (snd (evenOrOdd-Even n p)) (snd (evenOrOdd-Even m q))

  -ₕ^-EvenOdd : (isEven n ≡ true) → (isEven m ≡ false) →
                 (x : coHom (m +' n) A) → (-ₕ^ n · m) x ≡ x
  -ₕ^-EvenOdd p q x = cong₂ (λ X Y → -ₕ^-gen n m X Y x) (snd (evenOrOdd-Even n p)) (snd (evenOrOdd-Odd m q))

  -ₕ^-OddEven : (isEven n ≡ false) → (isEven m ≡ true) →
                 (x : coHom (m +' n) A) → (-ₕ^ n · m) x ≡ x
  -ₕ^-OddEven p q x = cong₂ (λ X Y → -ₕ^-gen n m X Y x) (snd (evenOrOdd-Odd n p)) (snd (evenOrOdd-Even m q))

  -ₕ^-OddOdd : (isEven n ≡ false) → (isEven m ≡ false) →
                 (x : coHom (m +' n) A) → (-ₕ^ n · m) x ≡ -ₕ x
  -ₕ^-OddOdd p q x = cong₂ (λ X Y → -ₕ^-gen n m X Y x) (snd (evenOrOdd-Odd n p)) (snd (evenOrOdd-Odd m q))
