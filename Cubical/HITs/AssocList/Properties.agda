{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.AssocList.Properties where

open import Cubical.HITs.AssocList.Base as AL
open import Cubical.Foundations.Everything
open import Cubical.HITs.FiniteMultiset as FMS
open import Cubical.Data.Nat   using (ℕ; zero; suc; _+_)

private
  variable
    ℓ : Level
    A : Type₀



multiPer : (a b : A) (m n : ℕ) (xs : AssocList A)
          → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
multiPer a b zero n xs = del a (⟨ b , n ⟩∷ xs) ∙ cong (λ ys → ⟨ b , n ⟩∷ ys) (sym (del a xs))
multiPer a b (suc m) zero xs = cong (λ ys → ⟨ a , suc m ⟩∷ ys) (del b xs) ∙ sym (del b (⟨ a , suc m ⟩∷ xs))
multiPer a b (suc m) (suc n) xs =

 ⟨ a , suc m ⟩∷ ⟨ b , suc n ⟩∷ xs               ≡⟨ sym (agg a 1 m (⟨ b , suc n ⟩∷ xs)) ⟩
 ⟨ a , 1 ⟩∷ ⟨ a , m ⟩∷ ⟨ b , suc n ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (multiPer a b m (suc n) xs) ⟩
 ⟨ a , 1 ⟩∷ ⟨ b , suc n ⟩∷ ⟨ a , m ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (sym (agg b 1 n (⟨ a , m ⟩∷ xs))) ⟩
 ⟨ a , 1 ⟩∷ ⟨ b , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs ≡⟨ per a b (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ys) (multiPer b a n m xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (agg a 1 m (⟨ b , n ⟩∷ xs)) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , suc m ⟩∷ ⟨ b , n ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (multiPer a b (suc m) n xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , suc m ⟩∷ xs        ≡⟨ agg b 1 n (⟨ a , suc m ⟩∷ xs) ⟩
 ⟨ b , suc n ⟩∷ ⟨ a , suc m ⟩∷ xs               ∎





-- Show that association lists and finite multisets are equivalent
multi-∷ : A → ℕ → FMSet A → FMSet A
multi-∷ x zero xs = xs
multi-∷ x (suc n) xs = x ∷ multi-∷ x n xs

multi-∷-agg : (x : A) (m n : ℕ) (b : FMSet A) → multi-∷ x m (multi-∷ x n b) ≡ multi-∷ x (m + n) b
multi-∷-agg x zero n b = refl
multi-∷-agg x (suc m) n b i = x ∷ (multi-∷-agg x m n b i)

AL→FMS : AssocList A → FMSet A
AL→FMS = AL.Rec.f FMS.trunc [] multi-∷ comm multi-∷-agg λ _ _ → refl


FMS→AL : FMSet A → AssocList A
FMS→AL = FMS.Rec.f AL.trunc ⟨⟩ (λ x xs → ⟨ x , 1 ⟩∷ xs) per



AL→FMS∘FMS→AL≡id : section {A = AssocList A} AL→FMS FMS→AL
AL→FMS∘FMS→AL≡id = FMS.ElimProp.f (FMS.trunc _ _) refl (λ x p → cong (λ ys → x ∷ ys) p)


-- need a little lemma for other direction
multi-∷-id : (x : A) (n : ℕ) (u : FMSet A)
            → FMS→AL (multi-∷ x n u) ≡ ⟨ x , n ⟩∷ FMS→AL u
multi-∷-id x zero u = sym (del x (FMS→AL u))
multi-∷-id x (suc n) u = FMS→AL (multi-∷ x (suc n) u)     ≡⟨ cong (λ ys → ⟨ x , 1 ⟩∷ ys) (multi-∷-id x n u) ⟩
                         ⟨ x , 1 ⟩∷ ⟨ x , n ⟩∷ (FMS→AL u) ≡⟨ agg x 1 n (FMS→AL u) ⟩
                         ⟨ x , (suc n) ⟩∷ (FMS→AL u)      ∎

FMS→AL∘AL→FMS≡id : retract {A = AssocList A} AL→FMS FMS→AL
FMS→AL∘AL→FMS≡id = AL.ElimProp.f (AL.trunc _ _) refl (λ x n {xs} p → (multi-∷-id x n (AL→FMS xs)) ∙ cong (λ ys → ⟨ x , n ⟩∷ ys) p)




AssocList≃FMSet : AssocList A ≃ FMSet A
AssocList≃FMSet = isoToEquiv (iso AL→FMS FMS→AL AL→FMS∘FMS→AL≡id FMS→AL∘AL→FMS≡id)


AssocList≡FMSet : AssocList A ≡ FMSet A
AssocList≡FMSet = ua AssocList≃FMSet
