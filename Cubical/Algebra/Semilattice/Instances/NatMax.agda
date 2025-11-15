{-

  ℕ with max forms a join-semilattice.
  This gives us a Max-operation for FinVec's of naturals
  and useful lemmas about it.

-}

module Cubical.Algebra.Semilattice.Instances.NatMax where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base as ⊥
open import Cubical.Data.FinData hiding (snotz)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.Semilattice.Base


open SemilatticeStr

private
  variable
    ℓ ℓ' : Level

maxSemilatticeStr : SemilatticeStr ℕ
ε maxSemilatticeStr = 0
_·_ maxSemilatticeStr = max
isSemilattice maxSemilatticeStr = makeIsSemilattice isSetℕ maxAssoc maxRId maxComm maxIdem
  where
  maxAssoc : (x y z : ℕ) → max x (max y z) ≡ max (max x y) z
  maxAssoc zero y z = refl
  maxAssoc (suc x) zero z = refl
  maxAssoc (suc x) (suc y) zero = maxSuc ∙ cong (λ p → max p _) (sym (maxSuc {x} {y}))
  maxAssoc (suc x) (suc y) (suc z) =
    max (suc x) (max (suc y) (suc z)) ≡⟨ cong (max _) (maxSuc {y} {z}) ⟩
    max (suc x) (suc (max y z))       ≡⟨ maxSuc ⟩
    suc (max x (max y z))             ≡⟨ cong suc (maxAssoc x y z) ⟩
    suc (max (max x y) z)             ≡⟨ sym maxSuc ⟩
    max (suc (max x y)) (suc z)       ≡⟨ cong (λ p → max p _) (sym (maxSuc {x} {y})) ⟩
    max (max (suc x) (suc y)) (suc z) ∎

  maxRId : (x : ℕ) → max x 0 ≡ x
  maxRId zero = refl
  maxRId (suc x) = refl

  maxIdem : (x : ℕ) → max x x ≡ x
  maxIdem zero = refl
  maxIdem (suc x) = maxSuc ∙ cong suc (maxIdem x)


--characterisation of inequality
open JoinSemilattice (ℕ , maxSemilatticeStr) renaming (_≤_ to _≤max_)

≤max→≤ℕ : ∀ x y → x ≤max y → x ≤ℕ y
≤max→≤ℕ zero y _ = zero-≤
≤max→≤ℕ (suc x) zero p = ⊥.rec (snotz p)
≤max→≤ℕ (suc x) (suc y) p = let (k , q) = ≤max→≤ℕ x y (cong predℕ (sym maxSuc ∙ p)) in
                            k , +-suc k x ∙ cong suc q

≤ℕ→≤max :  ∀ x y → x ≤ℕ y → x ≤max y
≤ℕ→≤max zero y _ = refl
≤ℕ→≤max (suc x) zero p = ⊥.rec (¬-<-zero p)
≤ℕ→≤max (suc x) (suc y) (k , p) = maxSuc ∙ cong suc (≤ℕ→≤max x y (k , q))
  where
  q : k +ℕ x ≡ y
  q = cong predℕ (sym (+-suc k x) ∙ p)


-- big max and all results with right inequality
open MonoidBigOp (Semilattice→Monoid (ℕ , maxSemilatticeStr))

Max = bigOp

ind≤Max :  {n : ℕ} (U : FinVec ℕ n) (i : Fin n) → U i ≤ℕ Max U
ind≤Max U i = ≤max→≤ℕ _ _ (ind≤bigOp U i)

MaxIsMax : {n : ℕ} (U : FinVec ℕ n) (x : ℕ) → (∀ i → U i ≤ℕ x) → Max U ≤ℕ x
MaxIsMax U x h = ≤max→≤ℕ _ _ (bigOpIsMax U x λ i → ≤ℕ→≤max _ _ (h i))

≤-MaxExt : {n : ℕ} (U W : FinVec ℕ n) → (∀ i → U i ≤ℕ W i) → Max U ≤ℕ Max W
≤-MaxExt U W h = ≤max→≤ℕ _ _ (≤-bigOpExt U W λ i → ≤ℕ→≤max _ _ (h i))
