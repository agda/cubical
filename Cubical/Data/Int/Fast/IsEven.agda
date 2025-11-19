module Cubical.Data.Int.Fast.IsEven where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
  using (ℕ ; zero ;  suc ; +-zero ; +-suc ; injSuc ; +-comm ; snotz ; znots ; ·-distribˡ)
  renaming
  (_+_    to _+ℕ_ ;
   _·_    to _·ℕ_ ;
   isEven to isEvenℕ ;
   isOdd  to isOddℕ)
import Cubical.Data.Nat.IsEven as ℕeven

open import Cubical.Data.Int.Base as ℤ
  hiding (_+_ ; _·_ ; _-_ ; _ℕ-_ ; sumFinℤ ; sumFinℤId)
open import Cubical.Data.Int.Fast.Base as ℤ
open import Cubical.Data.Int.Fast.Properties
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int.Fast

open GroupStr (snd BoolGroup) using ()
  renaming ( _·_ to _+Bool_ )

-----------------------------------------------------------------------------
-- Lemma over ℤ

2negsuc : (k : ℕ) → 2 · negsuc k ≡ negsuc (1 +ℕ 2 ·ℕ k)
2negsuc k = cong negsuc (+-suc k (k +ℕ zero))

1+2kNegsuc : (k : ℕ) → 1 + 2 · negsuc k ≡ negsuc (2 ·ℕ k)
1+2kNegsuc k = cong (λ X → 1 + X)
                    ( 2negsuc k
                    ∙ cong negsuc (+-comm 1 (2 ·ℕ k))
                    ∙ negsuc+ (2 ·ℕ k) 1
                    ∙ +Comm (negsuc (2 ·ℕ k)) (- 1))
               ∙ sym (pos0+ (negsuc (2 ·ℕ k)))

1+2kPos : (k : ℕ) → pos (1 +ℕ 2 ·ℕ k) ≡ 1 + 2 · (pos k)
1+2kPos k = refl

-- isEven → 2k / isOdd → 1 + 2k
isEvenTrue : (a : ℤ) → (isEven a ≡ true) → Σ[ m ∈ ℤ ] a ≡ (2 · m)
isEvenTrue (pos n) p = (pos k) , cong pos pp
  where
  k = fst (ℕeven.isEvenTrue n p)
  pp = snd (ℕeven.isEvenTrue n p)
isEvenTrue (negsuc n) p = (negsuc k) , cong negsuc pp ∙ sym (2negsuc k)
  where
  k = fst (ℕeven.isOddTrue n p)
  pp = snd (ℕeven.isOddTrue n p)

isEvenFalse : (a : ℤ) → (isEven a ≡ false) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m)
isEvenFalse (pos n) p = (pos k) , (cong pos pp)
  where
  k = fst (ℕeven.isEvenFalse n p)
  pp = snd (ℕeven.isEvenFalse n p)
isEvenFalse (negsuc n) p = (negsuc k) , (cong negsuc pp ∙ sym (1+2kNegsuc k))
  where
  k = fst (ℕeven.isOddFalse n p)
  pp = snd (ℕeven.isOddFalse n p)


-- 2k → isEven / 1 + 2k → isOdd
trueIsEven : (a : ℤ)  → Σ[ m ∈ ℤ ] a ≡ (2 · m) → (isEven a ≡ true)
trueIsEven (pos n) (pos m , p) = ℕeven.trueIsEven n (m , injPos p)
trueIsEven (pos n) (negsuc m , p) = ⊥.rec (posNotnegsuc n (1 +ℕ 2 ·ℕ m) (p ∙ 2negsuc m))
trueIsEven (negsuc n) (pos m , p) = ⊥.rec (negsucNotpos n (2 ·ℕ m) p)
trueIsEven (negsuc n) (negsuc m , p) = ℕeven.¬IsEvenFalse n (ℕeven.falseIsEven n
                                       (m , (injNegsuc (p ∙ 2negsuc m))))

falseIsEven : (a : ℤ) → Σ[ m ∈ ℤ ] a ≡ 1 + (2 · m) → isEven a ≡ false
falseIsEven (pos n) (pos m , p) = ℕeven.falseIsEven n (m , injPos p)
falseIsEven (pos n) (negsuc m , p) = ⊥.rec (posNotnegsuc n (2 ·ℕ m) (p ∙ 1+2kNegsuc m))
falseIsEven (negsuc n) (pos m , p) = ⊥.rec (negsucNotpos n (1 +ℕ 2 ·ℕ m) (p ∙ sym (1+2kPos m)))
falseIsEven (negsuc n) (negsuc m , p) = ℕeven.¬IsEvenTrue n (ℕeven.trueIsEven n (m , (injNegsuc (p ∙ 1+2kNegsuc m ))))


-- Value of isEven (x + y)  depending on IsEven x, IsEven y
isOddIsOdd→IsEven : (x y : ℤ) → isEven x ≡ false → isEven y ≡ false → isEven (x + y) ≡ true
isOddIsOdd→IsEven x y px py = trueIsEven (x + y) ((1 + k + l) , cong₂ _+_ qk ql ∙ sym helper)
  where
  k  = fst (isEvenFalse x px)
  qk = snd (isEvenFalse x px)
  l  = fst (isEvenFalse y py)
  ql = snd (isEvenFalse y py)
  helper : 2 · ((1 + k) + l) ≡ (1 + 2 · k) + (1 + 2 · l)
  helper = 2 · ((1 + k) + l)         ≡⟨ ·DistR+ 2 (1 + k) l ⟩
           2 · (1 + k) + 2 · l       ≡⟨ cong (_+ 2 · l) (·DistR+ 2 1 k) ⟩
           (1 + 1 + 2 · k) + 2 · l   ≡⟨ cong (_+ 2 · l) (sym (+Assoc 1 1 (2 · k))) ⟩
           1 + (1 + 2 · k) + 2 · l   ≡⟨ cong (λ r → 1 + r + 2 · l) (+Comm 1 (2 · k)) ⟩
           1 + (2 · k + 1) + 2 · l   ≡⟨ cong (_+ 2 · l) (+Assoc 1 (2 · k) 1) ⟩
           ((1 + 2 · k) + 1) + 2 · l ≡⟨ sym (+Assoc (1 + 2 · k) 1 (2 · l)) ⟩
           (1 + 2 · k) + (1 + 2 · l) ∎

isOddIsEven→IsOdd : (x y : ℤ) → isEven x ≡ false → isEven y ≡ true → isEven (x + y) ≡ false
isOddIsEven→IsOdd x y px py = falseIsEven (x + y) ((k + l) , ( cong₂ _+_ qk ql ∙ helper))
  where
  k  = fst (isEvenFalse x px)
  qk = snd (isEvenFalse x px)
  l  = fst (isEvenTrue y py)
  ql = snd (isEvenTrue y py)
  helper : _
  helper = (1 + 2 · k) + 2 · l ≡⟨ sym (+Assoc 1 (2 · k) (2 · l)) ⟩
           1 + (2 · k + 2 · l) ≡⟨ cong (1 +_) ( sym (·DistR+ 2 k l)) ⟩
           1 + 2 · (k + l)     ∎

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
isEven-pres+ x y with (dichotomyBoolSym (isEven x)) | dichotomyBoolSym (isEven y)
... | inl xf | inl yf = isOddIsOdd→IsEven x y xf yf ∙ sym (cong₂ _+Bool_ xf yf)
... | inl xf | inr yt = isOddIsEven→IsOdd x y xf yt ∙ sym (cong₂ _+Bool_ xf yt)
... | inr xt | inl yf = isEvenIsOdd→IsOdd x y xt yf ∙ sym (cong₂ _+Bool_ xt yf)
... | inr xt | inr yt = isEvenIsEven→IsEven x y xt yt ∙ sym (cong₂ _+Bool_ xt yt)

isEven-GroupMorphism : IsGroupHom (snd ℤGroup) isEven (snd BoolGroup)
isEven-GroupMorphism = makeIsGroupHom isEven-pres+
