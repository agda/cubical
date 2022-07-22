{-# OPTIONS --safe #-}
module Cubical.Data.Int.IsEven where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
  using (ℕ ; zero ;  suc ; +-zero ; +-suc ; injSuc ; +-comm ;snotz ; znots ; ·-distribˡ)
  renaming  (_+_ to _+ℕ_ ; _·_ to _·ℕ_ ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Int
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Bool




open GroupStr (snd BoolGroup)
  renaming ( _·_ to _+Bool_ )

-- lemma over Bool
True⊎False : (x : Bool) → (x ≡ false) ⊎ (x ≡ true)
True⊎False false = inl refl
True⊎False true = inr refl

-----------------------------------------------------------------------------
-- Lemma over ℕ

-- negation result
¬IsEvenFalse : (n : ℕ) → (isEvenℕ n ≡ false) → isOddℕ n ≡ true
¬IsEvenFalse zero p = ⊥.rec (true≢false p)
¬IsEvenFalse (suc zero) p = refl
¬IsEvenFalse (suc (suc n)) p = ¬IsEvenFalse n p

¬IsEvenTrue : (n : ℕ) → (isEvenℕ n ≡ true) → isOddℕ n ≡ false
¬IsEvenTrue zero p = refl
¬IsEvenTrue (suc zero) p = ⊥.rec (false≢true p)
¬IsEvenTrue (suc (suc n)) p = ¬IsEvenTrue n p

¬IsOddFalse : (n : ℕ) → (isOddℕ n ≡ false) → isEvenℕ n ≡ true
¬IsOddFalse zero p = refl
¬IsOddFalse (suc zero) p = ⊥.rec (true≢false p)
¬IsOddFalse (suc (suc n)) p = ¬IsOddFalse n p

¬IsOddTrue : (n : ℕ) → (isOddℕ n ≡ true) → isEvenℕ n ≡ false
¬IsOddTrue zero p = ⊥.rec (false≢true p)
¬IsOddTrue (suc zero) p = refl
¬IsOddTrue (suc (suc n)) p = ¬IsOddTrue n p


-- isEven → 2k / isOdd → 1 + 2k
isEvenℕTrue : (n : ℕ) → (isEvenℕ n ≡ true) → Σ[ m ∈ ℕ ] n ≡ (2 ·ℕ m)
isOddℕTrue : (n : ℕ) → (isOddℕ n ≡ true) → Σ[ m ∈ ℕ ] n ≡ 1 +ℕ (2 ·ℕ m)
isEvenℕTrue zero p = 0 , refl
isEvenℕTrue (suc n) p = (suc k) , cong suc pp ∙ cong suc (sym (+-suc _ _))
       where
       k = fst (isOddℕTrue n p)
       pp = snd (isOddℕTrue n p)
isOddℕTrue zero p = ⊥.rec (false≢true p)
isOddℕTrue (suc n) p = (fst (isEvenℕTrue n p)) , (cong suc (snd (isEvenℕTrue n p)))

isEvenℕFalse : (n : ℕ) → (isEvenℕ n ≡ false) → Σ[ m ∈ ℕ ] n ≡ 1 +ℕ (2 ·ℕ m)
isEvenℕFalse n p = isOddℕTrue n (¬IsEvenFalse n p)

isOddℕFalse : (n : ℕ) → (isOddℕ n ≡ false) → Σ[ m ∈ ℕ ] n ≡ (2 ·ℕ m)
isOddℕFalse n p = isEvenℕTrue n (¬IsOddFalse n p)


-- 2k -> isEven
trueIsEvenℕ : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (2 ·ℕ m) → (isEvenℕ n ≡ true)
trueIsEvenℕ zero (m , p) = refl
trueIsEvenℕ (suc zero) (zero , p) = ⊥.rec (snotz p)
trueIsEvenℕ (suc zero) (suc m , p) = ⊥.rec (znots (injSuc (p ∙ cong suc (+-suc _ _))))
trueIsEvenℕ (suc (suc n)) (zero , p) = ⊥.rec (snotz p)
trueIsEvenℕ (suc (suc n)) (suc m , p) = trueIsEvenℕ n (m , (injSuc (injSuc (p ∙ cong suc (+-suc _ _)))))

falseIsEvenℕ : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (1 +ℕ 2 ·ℕ m) → (isEvenℕ n ≡ false)
falseIsEvenℕ zero (m , p) = ⊥.rec (znots p)
falseIsEvenℕ (suc n) (m , p) = ¬IsEvenTrue n (trueIsEvenℕ n (m , (injSuc p)))


-----------------------------------------------------------------------------
-- Lemma over ℤ

2negsuc : (k : ℕ) → 2 · negsuc k ≡ negsuc (1 +ℕ 2 ·ℕ k)
2negsuc k = sym
            (negsuc (1 +ℕ 2 ·ℕ k) ≡⟨ refl ⟩
             neg (suc (1 +ℕ 2 ·ℕ k))        ≡⟨ cong neg refl ⟩
             neg (2 +ℕ 2 ·ℕ k)              ≡⟨ cong neg (·-distribˡ 2 1 k) ⟩
             neg (2 ·ℕ (suc k))              ≡⟨ refl ⟩
             - pos (2 ·ℕ (suc k))            ≡⟨ cong -_ (pos·pos 2 (suc k)) ⟩
             - (2 · pos (suc k))              ≡⟨ -DistR· 2 (pos (suc k)) ⟩
             2 · neg (suc k)                  ≡⟨ refl ⟩
             2 · negsuc k ∎)

1+2kNegsuc : (k : ℕ) → 1 + 2 · negsuc k ≡ negsuc (2 ·ℕ k)
1+2kNegsuc k = cong (λ X → 1 + X)
                    ( 2negsuc k
                    ∙ cong negsuc (+-comm 1 (2 ·ℕ k))
                    ∙ negsuc+ (2 ·ℕ k) 1
                    ∙ +Comm (negsuc (2 ·ℕ k)) (- 1))
               ∙ +Assoc 1 (- 1) (negsuc (2 ·ℕ k))
               ∙ sym (pos0+ (negsuc (2 ·ℕ k)))

1+2kPos : (k : ℕ) → pos (1 +ℕ 2 ·ℕ k) ≡ 1 + 2 · (pos k)
1+2kPos k = pos+ 1 (2 ·ℕ k) ∙ cong (λ X → 1 + X) (pos·pos 2 k)

-- isEven → 2k / isOdd → 1 + 2k
isEvenTrue : (a : ℤ) → (isEven a ≡ true) → Σ[ m ∈ ℤ ] a ≡ (2 · m)
isEvenTrue (pos n) p = (pos k) , (cong pos pp ∙ pos·pos 2 k )
  where
  k = fst (isEvenℕTrue n p)
  pp = snd (isEvenℕTrue n p)
isEvenTrue (negsuc n) p = (negsuc k) , cong negsuc pp ∙ sym (2negsuc k)
  where
  k = fst (isOddℕTrue n p)
  pp = snd (isOddℕTrue n p)

isEvenFalse : (a : ℤ) → (isEven a ≡ false) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m)
isEvenFalse (pos n) p = (pos k) , (cong pos pp ∙ 1+2kPos k)
  where
  k = fst (isEvenℕFalse n p)
  pp = snd (isEvenℕFalse n p)
isEvenFalse (negsuc n) p = (negsuc k) , (cong negsuc pp ∙ sym (1+2kNegsuc k))
  where
  k = fst (isOddℕFalse n p)
  pp = snd (isOddℕFalse n p)


-- 2k → isEven / 1 + 2k → isOdd
trueIsEven : (a : ℤ)  → Σ[ m ∈ ℤ ] a ≡ (2 · m) → (isEven a ≡ true)
trueIsEven (pos n) (pos m , p) = trueIsEvenℕ n (m , injPos (p ∙ sym (pos·pos 2 m)))
trueIsEven (pos n) (negsuc m , p) = ⊥.rec (posNotnegsuc n (1 +ℕ 2 ·ℕ m) (p ∙ 2negsuc m))
trueIsEven (negsuc n) (pos m , p) = ⊥.rec (negsucNotpos n (2 ·ℕ m) (p ∙ sym (pos·pos 2 m)))
trueIsEven (negsuc n) (negsuc m , p) = ¬IsEvenFalse n (falseIsEvenℕ n
                                       (m , (injNegsuc (p ∙ 2negsuc m))))

falseIsEven : (a : ℤ) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m) → isEven a ≡ false
falseIsEven (pos n) (pos m , p) = falseIsEvenℕ n
                                  (m , (injPos (p ∙ sym (1+2kPos m))))
falseIsEven (pos n) (negsuc m , p) = ⊥.rec (posNotnegsuc n (2 ·ℕ m) (p ∙ 1+2kNegsuc m))
falseIsEven (negsuc n) (pos m , p) = ⊥.rec (negsucNotpos n (1 +ℕ 2 ·ℕ m) (p ∙ sym (1+2kPos m)))
falseIsEven (negsuc n) (negsuc m , p) = ¬IsEvenTrue n (trueIsEvenℕ n (m , (injNegsuc (p ∙ 1+2kNegsuc m ))))


-- Value of isEven (x + y)  depending on IsEven x, IsEven y
isOddIsOdd→IsEven : (x y : ℤ) → isEven x ≡ false → isEven y ≡ false → isEven (x + y) ≡ true
isOddIsOdd→IsEven x y px py = trueIsEven (x + y) ((1 + k + l) , cong₂ _+_ qk ql ∙ sym helper)
  where
  k =  fst (isEvenFalse x px)
  qk = snd (isEvenFalse x px)
  l = fst (isEvenFalse y py)
  ql = snd (isEvenFalse y py)
  helper : 2 · ((1 + k) + l) ≡ (1 + 2 · k) + (1 + 2 · l)
  helper = 2 · ((1 + k) + l)        ≡⟨ ·DistR+ 2 (1 + k) l ⟩
           2 · (1 + k) + 2 · l      ≡⟨ cong (λ X → X + 2 · l)
                                            (·DistR+ 2 1 k ∙ sym (+Assoc 1 1 (2 · k)) ∙ +Comm 1 (1 + 2 · k)) ⟩
           ((1 + 2 · k) + 1) + 2 · l     ≡⟨ sym (+Assoc (1 + 2 · k) 1 (2 · l)) ⟩
           (1 + 2 · k) + (1 + 2 · l) ∎

isOddIsEven→IsOdd : (x y : ℤ) → isEven x ≡ false → isEven y ≡ true → isEven (x + y) ≡ false
isOddIsEven→IsOdd x y px py = falseIsEven (x + y) ((k + l) , ( cong₂ _+_ qk ql ∙ helper))
  where
  k =  fst (isEvenFalse x px)
  qk = snd (isEvenFalse x px)
  l = fst (isEvenTrue y py)
  ql = snd (isEvenTrue y py)
  helper : _
  helper = (1 + 2 · k) + 2 · l ≡⟨ sym (+Assoc 1 (2 · k) (2 · l)) ⟩
           1 + (2 · k + 2 · l) ≡⟨ cong (λ X → 1 + X) (sym (·DistR+ 2 k l)) ⟩
           1 + 2 · (k + l) ∎

isEvenIsOdd→IsOdd : (x y : ℤ) → isEven x ≡ true → isEven y ≡ false → isEven (x + y) ≡ false
isEvenIsOdd→IsOdd x y px py = cong isEven (+Comm x y) ∙ isOddIsEven→IsOdd y x py px

isEvenIsEven→IsEven : (x y : ℤ) → isEven x ≡ true → isEven y ≡ true → isEven (x + y) ≡ true
isEvenIsEven→IsEven x y px py = trueIsEven (x + y) ((k + l) , cong₂ _+_ qk ql ∙ sym (·DistR+ 2 k l))
  where
  k =  fst (isEvenTrue x px)
  qk = snd (isEvenTrue x px)
  l = fst (isEvenTrue y py)
  ql = snd (isEvenTrue y py)


-- Proof that isEven is morphism
isEven-pres+ : (x y : ℤ) → isEven (x + y) ≡ isEven x +Bool isEven y
isEven-pres+ x y with (True⊎False (isEven x)) | True⊎False (isEven y)
... | inl xf | inl yf = isOddIsOdd→IsEven x y xf yf ∙ sym (cong₂ _+Bool_ xf yf)
... | inl xf | inr yt = isOddIsEven→IsOdd x y xf yt ∙ sym (cong₂ _+Bool_ xf yt)
... | inr xt | inl yf = isEvenIsOdd→IsOdd x y xt yf ∙ sym (cong₂ _+Bool_ xt yf)
... | inr xt | inr yt = isEvenIsEven→IsEven x y xt yt ∙ sym (cong₂ _+Bool_ xt yt)
