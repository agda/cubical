{-# OPTIONS --safe #-}
module Cubical.Data.Int.IsEven where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
  using (ℕ ; zero ;  suc ; +-zero ; +-suc ; injSuc ; snotz ; znots ; ·-distribˡ)
  renaming  (_+_ to _+ℕ_ ; _·_ to _·ℕ_ ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Int
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Bool


-- prove that it is a morphism
module evenMorphism where

  open GroupStr (snd BoolGroup)
    renaming ( _·_ to _+Bool_ )

  -- lemma over Bool
  True⊎False : (x : Bool) → (x ≡ false) ⊎ (x ≡ true)
  True⊎False false = inl refl
  True⊎False true = inr refl

  -- lemma over ℕ
    -- neg result
  ¬IsEven : (n : ℕ) → (isEvenℕ n ≡ false) → isOddℕ n ≡ true
  ¬IsEven zero p = ⊥.rec (true≢false p)
  ¬IsEven (suc zero) p = refl
  ¬IsEven (suc (suc n)) p = ¬IsEven n p

  ¬IsOdd : (n : ℕ) → (isOddℕ n ≡ false) → isEvenℕ n ≡ true
  ¬IsOdd zero p = refl
  ¬IsOdd (suc zero) p = ⊥.rec (true≢false p)
  ¬IsOdd (suc (suc n)) p = ¬IsOdd n p

    -- isEven → 2k
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
  isEvenℕFalse n p = isOddℕTrue n (¬IsEven n p)

  isOddℕFalse : (n : ℕ) → (isOddℕ n ≡ false) → Σ[ m ∈ ℕ ] n ≡ (2 ·ℕ m)
  isOddℕFalse n p = isEvenℕTrue n (¬IsOdd n p)

    -- 2k -> isEven
  trueIsEvenℕ : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (2 ·ℕ m) → (isEvenℕ n ≡ true)
  trueIsEvenℕ zero (m , p) = refl
  trueIsEvenℕ (suc zero) (zero , p) = ⊥.rec (snotz p)
  trueIsEvenℕ (suc zero) (suc m , p) = ⊥.rec (znots (injSuc (p ∙ cong suc (+-suc _ _))))
  trueIsEvenℕ (suc (suc n)) (zero , p) = ⊥.rec (snotz p)
  trueIsEvenℕ (suc (suc n)) (suc m , p) = trueIsEvenℕ n (m , (injSuc (injSuc (p ∙ cong suc (+-suc _ _)))))

  falseIsEvenℕ : (n : ℕ) → Σ[ m ∈ ℕ ] n ≡ (1 +ℕ 2 ·ℕ m) → (isEvenℕ n ≡ false)
  falseIsEvenℕ = {!!}

  -- lemma over ℤ

  isEvenTrue : (a : ℤ) → (isEven a ≡ true) → Σ[ m ∈ ℤ ] a ≡ (2 · m)
  isEvenTrue (pos n) p = (pos k) , (cong pos pp ∙ pos+ k (k +ℕ 0) ∙ cong (λ X → pos k + pos X) (+-zero k))
    where
    k = fst (isEvenℕTrue n p)
    pp = snd (isEvenℕTrue n p)
  isEvenTrue (negsuc n) p = (negsuc k) , helper
    where
    k = fst (isOddℕTrue n p)
    pp = snd (isOddℕTrue n p)
    helper : negsuc n ≡ 2 · negsuc k
    helper = negsuc n                         ≡⟨ refl ⟩
             neg (suc n)                      ≡⟨ cong (λ X → neg (suc X)) pp ⟩
             neg (suc (1 +ℕ 2 ·ℕ k))        ≡⟨ cong neg refl ⟩
             neg (2 +ℕ 2 ·ℕ k)              ≡⟨ cong neg (·-distribˡ 2 1 k) ⟩
             neg (2 ·ℕ (suc k))              ≡⟨ refl ⟩
             - pos (2 ·ℕ (suc k))            ≡⟨ cong -_ (pos·pos 2 (suc k)) ⟩
             - (2 · pos (suc k))              ≡⟨ -DistR· 2 (pos (suc k)) ⟩
             2 · neg (suc k)                  ≡⟨ refl ⟩
             2 · negsuc k ∎

  isEvenFalse : (a : ℤ) → (isEven a ≡ false) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m)
  isEvenFalse = {!!}

  trueIsEven : (a : ℤ)  → Σ[ m ∈ ℤ ] a ≡ (2 · m) → (isEven a ≡ true)
  trueIsEven = {!!}

  falseIsEven : (a : ℤ) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m) → isEven a ≡ false
  falseIsEven = {!!}

  -- We compute isEven using its value table
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

  -- pres+
  isEven-pres+ : (x y : ℤ) → isEven (x + y) ≡ isEven x +Bool isEven y
  isEven-pres+ x y with (True⊎False (isEven x)) | True⊎False (isEven y)
  ... | inl xf | inl yf = isOddIsOdd→IsEven x y xf yf ∙ sym (cong₂ _+Bool_ xf yf)
  ... | inl xf | inr yt = isOddIsEven→IsOdd x y xf yt ∙ sym (cong₂ _+Bool_ xf yt)
  ... | inr xt | inl yf = isEvenIsOdd→IsOdd x y xt yf ∙ sym (cong₂ _+Bool_ xt yf)
  ... | inr xt | inr yt = isEvenIsEven→IsEven x y xt yt ∙ sym (cong₂ _+Bool_ xt yt)
