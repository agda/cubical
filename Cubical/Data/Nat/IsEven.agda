module Cubical.Data.Nat.IsEven where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Mod

-- negation result
¬IsEvenFalse : (n : ℕ) → (isEven n ≡ false) → isOdd n ≡ true
¬IsEvenFalse zero p = ⊥.rec (true≢false p)
¬IsEvenFalse (suc zero) p = refl
¬IsEvenFalse (suc (suc n)) p = ¬IsEvenFalse n p

¬IsEvenTrue : (n : ℕ) → (isEven n ≡ true) → isOdd n ≡ false
¬IsEvenTrue zero p = refl
¬IsEvenTrue (suc zero) p = ⊥.rec (false≢true p)
¬IsEvenTrue (suc (suc n)) p = ¬IsEvenTrue n p

¬IsOddFalse : (n : ℕ) → (isOdd n ≡ false) → isEven n ≡ true
¬IsOddFalse zero p = refl
¬IsOddFalse (suc zero) p = ⊥.rec (true≢false p)
¬IsOddFalse (suc (suc n)) p = ¬IsOddFalse n p

¬IsOddTrue : (n : ℕ) → (isOdd n ≡ true) → isEven n ≡ false
¬IsOddTrue zero p = ⊥.rec (false≢true p)
¬IsOddTrue (suc zero) p = refl
¬IsOddTrue (suc (suc n)) p = ¬IsOddTrue n p


-- isEven → 2k / isOdd → 1 + 2k
isEvenTrue : (n : ℕ) → (isEven n ≡ true) → Σ[ m ∈ ℕ ] n ≡ (2 · m)
isOddTrue : (n : ℕ) → (isOdd n ≡ true) → Σ[ m ∈ ℕ ] n ≡ 1 + (2 · m)
isEvenTrue zero p = 0 , refl
isEvenTrue (suc n) p = (suc k) , cong suc pp ∙ cong suc (sym (+-suc _ _))
       where
       k = fst (isOddTrue n p)
       pp = snd (isOddTrue n p)
isOddTrue zero p = ⊥.rec (false≢true p)
isOddTrue (suc n) p = (fst (isEvenTrue n p)) , (cong suc (snd (isEvenTrue n p)))

isEvenFalse : (n : ℕ) → (isEven n ≡ false) → Σ[ m ∈ ℕ ] n ≡ 1 + (2 · m)
isEvenFalse n p = isOddTrue n (¬IsEvenFalse n p)

isOddFalse : (n : ℕ) → (isOdd n ≡ false) → Σ[ m ∈ ℕ ] n ≡ (2 · m)
isOddFalse n p = isEvenTrue n (¬IsOddFalse n p)


-- 2k -> isEven
trueIsEven : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (2 · m) → (isEven n ≡ true)
trueIsEven zero (m , p) = refl
trueIsEven (suc zero) (zero , p) = ⊥.rec (snotz p)
trueIsEven (suc zero) (suc m , p) = ⊥.rec (znots (injSuc (p ∙ cong suc (+-suc _ _))))
trueIsEven (suc (suc n)) (zero , p) = ⊥.rec (snotz p)
trueIsEven (suc (suc n)) (suc m , p) = trueIsEven n (m , (injSuc (injSuc (p ∙ cong suc (+-suc _ _)))))

falseIsEven : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (1 + 2 · m) → (isEven n ≡ false)
falseIsEven zero (m , p) = ⊥.rec (znots p)
falseIsEven (suc n) (m , p) = ¬IsEvenTrue n (trueIsEven n (m , (injSuc p)))

-- Some lemma for EvenT and OddT

evenOrOdd-Even : (n : ℕ) → (isEven n ≡ true) → Σ[ x ∈ isEvenT n ] evenOrOdd n ≡ inl x
evenOrOdd-Even zero p = tt , refl
evenOrOdd-Even (suc zero) p = ⊥.rec (false≢true p)
evenOrOdd-Even (suc (suc n)) p = evenOrOdd-Even n p

evenOrOdd-Odd : (n : ℕ) → (isEven n ≡ false) → Σ[ x ∈ isOddT n ] evenOrOdd n ≡ inr x
evenOrOdd-Odd zero p = ⊥.rec (true≢false p)
evenOrOdd-Odd (suc zero) p = tt , refl
evenOrOdd-Odd (suc (suc n)) p = evenOrOdd-Odd n p

isEvenT→isEvenTrue : (n : ℕ) → isEvenT n → (isEven n ≡ true)
isEvenT→isEvenTrue zero x = refl
isEvenT→isEvenTrue (suc (suc n)) x = isEvenT→isEvenTrue n x

isEvenT→isOddFalse : (n : ℕ) → isEvenT n → (isOdd n ≡ false)
isEvenT→isOddFalse zero x = refl
isEvenT→isOddFalse (suc (suc n)) x = isEvenT→isOddFalse n x

isOddT→isEvenFalse : (n : ℕ) → isOddT n → (isEven n ≡ false)
isOddT→isEvenFalse (suc n) x = isEvenT→isOddFalse n x

isOddT→isOddTrue : (n : ℕ) → isOddT n → (isOdd n ≡ true)
isOddT→isOddTrue (suc n) x = isEvenT→isEvenTrue n x

------------

even+even≡even : (n m : ℕ) → isEvenT n → isEvenT m → isEvenT (n + m)
even+even≡even zero m p q = q
even+even≡even (suc (suc n)) m p q = even+even≡even n m p q

even+odd≡odd : (n m : ℕ) → isEvenT n → isOddT m → isOddT (n + m)
even+odd≡odd zero m p q = q
even+odd≡odd (suc (suc n)) m p q = even+odd≡odd n m p q

odd+even≡odd : (n m : ℕ) → isOddT n → isEvenT m → isOddT (n + m)
odd+even≡odd n m p q = subst isOddT (+-comm m n) (even+odd≡odd m n q p)

odd+odd≡even : (n m : ℕ) → isOddT n → isOddT m → isEvenT (n + m)
odd+odd≡even (suc n) (suc m) p q =
  subst isEvenT (cong suc (sym (+-suc n m)))
        (even+even≡even n m p q)

isEven·2 : (n : ℕ) → isEvenT (n + n)
isEven·2 zero = tt
isEven·2 (suc n) =
  subst isEvenT (cong suc (+-comm (suc n) n)) (isEven·2 n)

even·x≡even : (n m : ℕ) → isEvenT n → isEvenT (n · m)
even·x≡even zero m p = tt
even·x≡even (suc (suc n)) m p =
  subst isEvenT (sym (+-assoc m m (n · m)))
    (even+even≡even (m + m) (n · m) (isEven·2 m) (even·x≡even n m p))

x·even≡even : (n m : ℕ) → isEvenT m → isEvenT (n · m)
x·even≡even n m p = subst isEvenT (·-comm m n) (even·x≡even m n p)

odd·odd≡odd : (n m : ℕ) → isOddT n → isOddT m → isOddT (n · m)
odd·odd≡odd (suc n) (suc m) p q =
  subst isOddT t (even+even≡even m _ q
    (even+even≡even n _ p (even·x≡even n m p)))
  where
  t : suc (m + (n + n · m)) ≡ suc (m + n · suc m)
  t = cong suc (cong (m +_) (cong (n +_) (·-comm n m) ∙ ·-comm (suc m) n))

even≡odd→odd≡even : (n m : ℕ) → isEvenT n ≡ isOddT m → isOddT n ≡ isEvenT m
even≡odd→odd≡even zero zero p = sym p
even≡odd→odd≡even zero (suc zero) p = refl
even≡odd→odd≡even zero (suc (suc m)) p = even≡odd→odd≡even zero m p
even≡odd→odd≡even (suc zero) zero p = refl
even≡odd→odd≡even (suc zero) (suc zero) p = sym p
even≡odd→odd≡even (suc zero) (suc (suc m)) p = even≡odd→odd≡even (suc zero) m p
even≡odd→odd≡even (suc (suc n)) m p = even≡odd→odd≡even n m p

-- Relation to mod 2
isEvenT↔≡0 : (n : ℕ) → isEvenT n ↔ ((n mod 2) ≡ 0)
isEvenT↔≡0 zero .fst _ = refl
isEvenT↔≡0 zero .snd _ = tt
isEvenT↔≡0 (suc zero) .fst ()
isEvenT↔≡0 (suc zero) .snd = snotz
isEvenT↔≡0 (suc (suc n)) =
  comp↔ (isEvenT↔≡0 n)
    (subst (λ x → (modInd 1 n ≡ 0) ↔ (x ≡ 0))
      (sym (mod+mod≡mod 2 2 n
          ∙ cong (_mod 2) main ∙ mod-idempotent n)) id↔)
  where
  main : ((2 mod 2) + (n mod 2)) ≡ n mod 2
  main = cong (_+ (n mod 2)) (zero-charac 2)

isOddT↔≡1 : (n : ℕ) → isOddT n ↔ ((n mod 2) ≡ 1)
isOddT↔≡1 zero .fst ()
isOddT↔≡1 zero .snd x = snotz (sym x)
isOddT↔≡1 (suc zero) .fst _ = refl
isOddT↔≡1 (suc zero) .snd _ = tt
isOddT↔≡1 (suc (suc n)) =
  comp↔ (isOddT↔≡1 n)
    (subst (λ x → (modInd 1 n ≡ 1) ↔ (x ≡ 1))
      (sym (mod-idempotent n) ∙ sym (mod+mod≡mod 2 2 n)) id↔)

-- characterisation of even/odd iterations of involutions
module _ {ℓ} {A : Type ℓ} (invA : A → A)
         (invol : (a : A) → invA (invA a) ≡ a) where
  iterEvenInv : (k : ℕ) → isEvenT k → (a : A) → iter k invA a ≡ a
  iterEvenInv zero evk a = refl
  iterEvenInv (suc (suc k)) evk a =
    invol (iter k invA a) ∙ iterEvenInv k evk a

  iterOddInv : (k : ℕ) → isOddT k → (a : A) → iter k invA a ≡ invA a
  iterOddInv (suc k) p a = cong invA (iterEvenInv k p a)

  iter+iter : (k : ℕ) (a : A) → iter k invA (iter k invA a) ≡ a
  iter+iter k a = sym (iter+ k k invA a) ∙ iterEvenInv (k + k) (isEven·2 k) a

-- pointed versions
module _ {ℓ} {A : Pointed ℓ} (invA : A →∙ A)
         (invol : invA ∘∙ invA ≡ idfun∙ A) where
  private -- technical lemmas
    sqEven' : (k : ℕ) (p : isEvenT k)
      → iterEvenInv (fst invA) (funExt⁻ (cong fst invol)) k p (pt A)
       ≡ iter∙ k invA .snd
    sqEven' zero p = refl
    sqEven' (suc (suc k)) p =
        (rUnit _
        ∙ (λ i → ((λ j → fst (invol (~ i ∧ j)) (iter k (fst invA) (pt A)))
          ∙ (λ j → fst (invol (~ i)) (iterEvenInv (fst invA)
                       (funExt⁻ (λ i₁ → fst (invol i₁))) k p (pt A) j)))
          ∙ λ j → fst (invol (~ i ∨ j)) (pt A) )
        ∙ cong₂ _∙_ (sym (lUnit _))
                (rUnit (funExt⁻ (cong fst invol) (pt A))
                ∙ cong₂ _∙_ refl (rUnit refl)
               ∙ PathP→compPathL (symP (cong snd invol)))
        ∙ assoc (cong (fst invA) (cong (fst invA) (iterEvenInv (fst invA)
                                       (funExt⁻ (cong fst invol)) k p (pt A))))
              (cong (fst invA) (snd invA))
              (snd invA))
      ∙ cong₂ _∙_ (sym (cong-∙ (fst invA)
                       (cong (fst invA) (iterEvenInv (fst invA)
                                        (funExt⁻ (cong fst invol)) k p (pt A)))
                       (snd invA))
                 ∙ cong (congS (fst invA))
                  (cong₂ _∙_ (cong (cong (fst invA))
                  (sqEven' k p)) refl)) refl

    sqOdd' : (k : ℕ) (p : isOddT k)
      → iterOddInv (fst invA) (funExt⁻ (cong fst invol)) k p (pt A) ∙ snd invA
       ≡ iter∙ k invA .snd
    sqOdd' (suc zero) p = refl
    sqOdd' (suc (suc (suc k))) p =
      cong₂ _∙_ (cong (congS (fst invA))
        (sqEven' (suc (suc k)) p))
        refl

    sqEven : (k : ℕ) (p : isEvenT k)
      → Square (iterEvenInv (fst invA) (funExt⁻ (cong fst invol)) k p (pt A))
                refl (iter∙ k invA .snd) refl
    sqEven k p = sqEven' k p ◁ λ i j → iter∙ k invA .snd (i ∨ j)


    sqOdd : (k : ℕ) (p : isOddT k)
      → Square (iterOddInv (fst invA) (funExt⁻ (cong fst invol)) k p (pt A))
                refl (iter∙ k invA .snd) (snd invA)
    sqOdd k p = flipSquare (sym (sqOdd' k p)
      ◁ symP (compPath-filler' (iterOddInv (fst invA)
                                (funExt⁻ (cong (λ r → fst r) invol)) k p (pt A))
                               (snd invA)))

  iter∙EvenInv : (k : ℕ) → isEvenT k → iter∙ k invA ≡ idfun∙ A
  iter∙EvenInv k p i .fst x =
    iterEvenInv (fst invA) (funExt⁻ (cong fst invol)) k p x i
  iter∙EvenInv k p i .snd j = sqEven k p j i

  iter∙OddInv : (k : ℕ) → isOddT k → iter∙ k invA ≡ invA
  iter∙OddInv k p i .fst x =
    iterOddInv (fst invA) (funExt⁻ (cong fst invol)) k p x i
  iter∙OddInv k p i .snd j = sqOdd k p j i
