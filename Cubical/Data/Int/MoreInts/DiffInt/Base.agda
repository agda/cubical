module Cubical.Data.Int.MoreInts.DiffInt.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (+-comm ; +-assoc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int renaming (ℤ to Int)

rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ +ℕ b₁
    y = a₁ +ℕ b₀

ℤ = (ℕ × ℕ) / rel


-- Proof of equivalence between Int and DiffInt

private
  -- Prove all the identities for ℕ×ℕ first and use that to build to ℤ

  Int→ℕ×ℕ : Int → (ℕ × ℕ)
  Int→ℕ×ℕ (pos n)    = ( n    , zero  )
  Int→ℕ×ℕ (negsuc n) = ( zero , suc n )

  ℕ×ℕ→Int : (ℕ × ℕ) → Int
  ℕ×ℕ→Int(n , m) = n ℕ- m

  relInt→ℕ×ℕ : ∀ m n → rel (Int→ℕ×ℕ (m ℕ- n)) (m , n)
  relInt→ℕ×ℕ zero zero = refl
  relInt→ℕ×ℕ zero (suc n) = refl
  relInt→ℕ×ℕ (suc m) zero = refl
  relInt→ℕ×ℕ (suc m) (suc n) =
    fst (Int→ℕ×ℕ (m ℕ- n)) +ℕ suc n   ≡⟨ +-suc (fst (Int→ℕ×ℕ (m ℕ- n))) n ⟩
    suc (fst (Int→ℕ×ℕ (m ℕ- n)) +ℕ n) ≡⟨ cong suc (relInt→ℕ×ℕ m n) ⟩
    suc (m +ℕ snd (Int→ℕ×ℕ (m ℕ- n))) ∎

  Int→ℕ×ℕ→Int : ∀ n → ℕ×ℕ→Int (Int→ℕ×ℕ n) ≡ n
  Int→ℕ×ℕ→Int (pos n) = refl
  Int→ℕ×ℕ→Int (negsuc n) = refl

  ℕ×ℕ→Int→ℕ×ℕ : ∀ p → rel (Int→ℕ×ℕ (ℕ×ℕ→Int p)) p
  ℕ×ℕ→Int→ℕ×ℕ (p₀ , p₁) = relInt→ℕ×ℕ p₀ p₁

-- Now build to ℤ using the above

Int→ℤ : Int → ℤ
Int→ℤ n = [ Int→ℕ×ℕ n ]

ℤ→Int : ℤ → Int
ℤ→Int [ z ] = ℕ×ℕ→Int z
ℤ→Int(eq/ a b r i) = lemℤeq a b r i
  where lemℤeq : (a b : (ℕ × ℕ)) → rel a b → ℕ×ℕ→Int(a) ≡ ℕ×ℕ→Int(b)
        lemℤeq (a₀ , a₁) (b₀ , b₁) r = a₀ ℕ- a₁          ≡⟨ pos- a₀ a₁ ⟩
                pos a₀ - pos a₁                          ≡[ i ]⟨ ((pos a₀ - pos a₁) + -Cancel (pos b₁) (~ i)) ⟩
               (pos a₀ - pos a₁) + (pos b₁ - pos b₁)     ≡⟨ +Assoc (pos a₀ + (- pos a₁)) (pos b₁) (- pos b₁) ⟩
              ((pos a₀ - pos a₁) + pos b₁) - pos b₁      ≡[ i ]⟨ +Assoc (pos a₀) (- pos a₁) (pos b₁) (~ i) + (- pos b₁) ⟩
               (pos a₀ + ((- pos a₁) + pos b₁)) - pos b₁ ≡[ i ]⟨ (pos a₀ + +Comm (- pos a₁) (pos b₁) i) - pos b₁ ⟩
               (pos a₀ + (pos b₁ - pos a₁)) - pos b₁     ≡[ i ]⟨ +Assoc (pos a₀) (pos b₁) (- pos a₁) i + (- pos b₁)  ⟩
              ((pos a₀ + pos b₁) - pos a₁) - pos b₁      ≡[ i ]⟨ (pos+ a₀ b₁ (~ i) - pos a₁) - pos b₁ ⟩
               (pos (a₀ +ℕ b₁) - pos a₁) - pos b₁        ≡[ i ]⟨ (pos (r i) - pos a₁) - pos b₁ ⟩
               (pos (b₀ +ℕ a₁) - pos a₁) - pos b₁        ≡[ i ]⟨ (pos+ b₀ a₁ i - pos a₁) - pos b₁ ⟩
              ((pos b₀ + pos a₁) - pos a₁) - pos b₁      ≡[ i ]⟨ +Assoc (pos b₀) (pos a₁) (- pos a₁) (~ i) + (- pos b₁) ⟩
               (pos b₀ + (pos a₁ - pos a₁)) - pos b₁     ≡[ i ]⟨ (pos b₀ + (-Cancel (pos a₁) i)) - pos b₁ ⟩
                pos b₀ - pos b₁                          ≡[ i ]⟨ pos- b₀ b₁ (~ i) ⟩
                b₀ ℕ- b₁                                 ∎
ℤ→Int(squash/ x x₀ p q i j) = isSetℤ (ℤ→Int x) (ℤ→Int x₀) (cong ℤ→Int p) (cong ℤ→Int q) i j

Int→ℤ→Int : ∀ z → ℤ→Int (Int→ℤ z) ≡ z
Int→ℤ→Int (pos n)    = refl
Int→ℤ→Int (negsuc n) = refl

ℤ→Int→ℤ : ∀ z → Int→ℤ (ℤ→Int z) ≡ z
ℤ→Int→ℤ = elimProp (λ z → squash/ (Int→ℤ (ℤ→Int z)) z) ℕ×ℕprf
  where ℕ×ℕprf : (a : ℕ × ℕ) → Int→ℤ (ℤ→Int [ a ]) ≡ [ a ]
        ℕ×ℕprf (a , b) = eq/ (Int→ℕ×ℕ (ℕ×ℕ→Int (a , b))) (a , b) (ℕ×ℕ→Int→ℕ×ℕ (a , b))

Int≡DiffInt : Int ≡ ℤ
Int≡DiffInt = isoToPath (iso Int→ℤ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int)
