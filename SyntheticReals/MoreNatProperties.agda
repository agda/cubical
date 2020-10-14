{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.MoreNatProperties where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)

open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Function.Base using (_$_)

open import Cubical.Data.Nat hiding (min)
-- open import Cubical.Data.Nat.Properties hiding (min)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s)

min : ℕ → ℕ → ℕ
min a b with a ≟ b
... | lt a<b = a
... | eq a≡b = a
... | gt b<a = b

max : ℕ → ℕ → ℕ
max a b with a ≟ b
... | lt a<b = b
... | eq a≡b = a
... | gt b<a = a

-- to make use of `it` to find proofs for `Fin k`:
module FinInstances where
  open import Function.Base using (it) public
  instance
    z≤n' : ∀ {n}                 → zero  ≤ n
    z≤n' {n} = z≤n
    s≤s' : ∀ {m n} {{m≤n : m ≤ n}} → suc m ≤ suc n
    s≤s' {m} {n} {{m≤n}} = s≤s m≤n

¬1<0 : ¬(1 < 0)
¬1<0 (k , p) = snotz (sym (+-suc k 1) ∙ p)

suc-preserves-< : ∀{x y} → x < y → suc x < suc y
suc-preserves-< {x} {y} p = s≤s p
suc-reflects-< : ∀{x y} → suc x < suc y → x < y
suc-reflects-< {x} {y} (k , p) = k , (injSuc (sym (+-suc k (suc x)) ∙ p))

¬[k+x<k] : ∀ k x → ¬(k + x < k)
¬[k+x<k] k x (z , p) = snotz $ sym $ inj-m+ {k} {0} (+-zero k ∙ sym p ∙ +-suc z (k + x) ∙ (λ i → suc (+-comm z (k + x) i)) ∙ (λ i → suc (+-assoc k x z (~ i))) ∙ sym (+-suc k (x + z)))

-- import MoreLogic
open import SyntheticReals.MoreLogic.Reasoning

<-asymʷ : ∀ a b → a < b → ¬(b < a)
<-asymʷ a b a<b = ¬m<m ∘ <-trans a<b

{-
<-asym : ∀ a b → a < b → ¬(b < a)
<-asym a b (k , p) (l , q) = snotz $ inj-m+ {a} ((sym γ ∙ transport (λ i → l + suc (p (~ i)) ≡ a) q) ∙ sym (+-zero a))
  where
    γ = (
      l + suc (k + suc a)   ≡⟨ ( λ i → l + suc (+-suc k a i)) ⟩
      l + suc (suc (k + a)) ≡⟨ ( λ i → l + suc (suc (+-comm k a i)) ) ⟩
      l + suc (suc (a + k)) ≡⟨ ( λ i → l + suc (+-suc a k (~ i))) ⟩
      l + suc (a + suc k)   ≡⟨ ( λ i → l + (+-suc a (suc k) (~ i))) ⟩
      l + (a + suc (suc k)) ≡⟨ +-assoc l a (suc (suc k)) ⟩
      (l + a) + suc (suc k) ≡⟨ (λ i → +-comm l a i + suc (suc k) ) ⟩
      (a + l) + suc (suc k) ≡⟨ sym $ +-assoc a l (suc (suc k)) ⟩
      a + (l + suc (suc k)) ≡⟨ (λ i → a + +-suc l (suc k) i) ⟩
      a + suc (l + suc k)   ∎)
-}

<>-implies-≡ : ∀ a b → a ≤ b → b ≤ a → a ≡ b
<>-implies-≡ a b (n , p) (m , q) with m+n≡0→m≡0×n≡0 {m} {n} (m+n≡n→m≡0 γ)
  where γ = sym (+-assoc m n a) ∙ (λ i → m + p i) ∙ q
... | m≡0 , n≡0 = (λ i → n≡0 (~ i) + a) ∙ p

≟-sym : ∀ a b → Trichotomy a b → Trichotomy b a
≟-sym a b (lt x) = gt x
≟-sym a b (eq x) = eq (sym x)
≟-sym a b (gt x) = lt x

-- NOTE: this is an ingedience to disprove
--         isComplex ≤ₙₗ isRat
--       which normalizes to
--         Σ[ k ∈ ℕ ] k + 4 ≡ 2
--       and is the same as
--         4 ≤ 2
--       so more elegantly would be
--         ∀ x k → x < x + suc k
--       and turn this into
--         ∀ x k → ¬ (x + suc k ≤ x)
k+x+sy≢x : ∀ k x y → ¬(k + (x + suc y) ≡ x)
k+x+sy≢x k x y p = snotz $ sym (+-suc k y) ∙ inj-m+ {x} (+-assoc x k (suc y) ∙ (λ i → (+-comm x k) i + (suc y)) ∙ sym (+-assoc k x (suc y)) ∙ p ∙ sym (+-zero x))

0≤x : ∀ x → 0 ≤ x
0≤x zero =  0 , refl
0≤x (suc x) =  suc x , (λ i → suc (+-zero x i)) ∙ refl {x = suc x}
