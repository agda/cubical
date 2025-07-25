module Cubical.Data.Nat.IsEven where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum

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
