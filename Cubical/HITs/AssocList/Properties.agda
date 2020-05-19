{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.AssocList.Properties where

open import Cubical.HITs.AssocList.Base as AL
open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP
open import Cubical.HITs.FiniteMultiset as FMS
open import Cubical.Data.Nat   using (ℕ; zero; suc; _+_; +-assoc; isSetℕ)
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    ℓ : Level
    A : Type ℓ



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

FMSet≃AssocList : FMSet A ≃ AssocList A
FMSet≃AssocList = isoToEquiv (iso FMS→AL AL→FMS FMS→AL∘AL→FMS≡id AL→FMS∘FMS→AL≡id)


AssocList≡FMSet : AssocList A ≡ FMSet A
AssocList≡FMSet = ua AssocList≃FMSet




-- We want to define a multiset structure on AssocList A, we use the recursor to define the count-function
ALcount-⟨,⟩∷*-aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ → ℕ
ALcount-⟨,⟩∷*-aux a x (yes a≡x) n xs = n + xs
ALcount-⟨,⟩∷*-aux a x (no  a≢x) n xs = xs


ALcount-per*-aux :  (a x y : A) (xs : ℕ) (p : Dec (a ≡ x)) (q : Dec (a ≡ y))
                   →  ALcount-⟨,⟩∷*-aux a x p 1 (ALcount-⟨,⟩∷*-aux a y q 1 xs)
                    ≡ ALcount-⟨,⟩∷*-aux a y q 1 (ALcount-⟨,⟩∷*-aux a x p 1 xs)
ALcount-per*-aux a x y xs (yes a≡x) (yes a≡y) = refl
ALcount-per*-aux a x y xs (yes a≡x) (no  a≢y) = refl
ALcount-per*-aux a x y xs (no  a≢x) (yes a≡y) = refl
ALcount-per*-aux a x y xs (no  a≢x) (no  a≢y) = refl


ALcount-agg*-aux :  (a x : A) (m n xs : ℕ) (p : Dec (a ≡ x))
                   →  ALcount-⟨,⟩∷*-aux a x p m (ALcount-⟨,⟩∷*-aux a x p n xs)
                    ≡ ALcount-⟨,⟩∷*-aux a x p (m + n) xs
ALcount-agg*-aux a x m n xs (yes x≡a) = +-assoc m n xs
ALcount-agg*-aux a x m n xs (no  x≢a) = refl


ALcount-del*-aux :  (a x : A) (xs : ℕ) (p : Dec (a ≡ x))
                   →  ALcount-⟨,⟩∷*-aux a x p 0 xs ≡ xs
ALcount-del*-aux a x xs (yes a≡x) = refl
ALcount-del*-aux a x xs (no  a≢x) = refl



module _(discA : Discrete A) where
 setA = Discrete→isSet discA



 ALcount-⟨,⟩∷* : A → A → ℕ → ℕ → ℕ
 ALcount-⟨,⟩∷* a x n xs = ALcount-⟨,⟩∷*-aux a x (discA a x) n xs


 ALcount-per* :  (a x y : A) (xs : ℕ)
                →  ALcount-⟨,⟩∷* a x 1 (ALcount-⟨,⟩∷* a y 1 xs)
                 ≡ ALcount-⟨,⟩∷* a y 1 (ALcount-⟨,⟩∷* a x 1 xs)
 ALcount-per* a x y xs = ALcount-per*-aux a x y xs (discA a x) (discA a y)


 ALcount-agg* :  (a x : A) (m n xs : ℕ)
                →  ALcount-⟨,⟩∷* a x m (ALcount-⟨,⟩∷* a x n xs)
                 ≡ ALcount-⟨,⟩∷* a x (m + n) xs
 ALcount-agg* a x m n xs = ALcount-agg*-aux a x m n xs (discA a x)


 ALcount-del* :  (a x : A) (xs : ℕ) → ALcount-⟨,⟩∷* a x 0 xs ≡ xs
 ALcount-del* a x xs = ALcount-del*-aux a x xs (discA a x)


 ALcount : A → AssocList A → ℕ
 ALcount a = AL.Rec.f isSetℕ 0 (ALcount-⟨,⟩∷* a) (ALcount-per* a) (ALcount-agg* a) (ALcount-del* a)



 AL-with-str : Multi-Set A setA
 AL-with-str = (AssocList A , ⟨⟩ , ⟨_, 1 ⟩∷_ , ALcount)


-- We want to show that Al-with-str ≅ FMS-with-str as multiset-structures
 FMS→AL-isIso : multi-set-iso A setA (FMS-with-str discA) (AL-with-str) FMSet≃AssocList
 FMS→AL-isIso = refl , (λ a xs → refl) , φ
  where
  φ : ∀ a xs → FMScount discA a xs ≡ ALcount a (FMS→AL xs)
  φ a = FMS.ElimProp.f (isSetℕ _ _) refl ψ
   where
   χ :  (x : A) (xs ys : ℕ) (p : Dec (a ≡ x))
      → xs ≡ ys
      → FMScount-∷*-aux a x p xs ≡ ALcount-⟨,⟩∷*-aux a x p 1 ys
   χ x xs ys (yes p) q = cong suc q
   χ x xs ys (no ¬p) q = q

   ψ :  (x : A) {xs : FMSet A}
      → FMScount discA a xs ≡ ALcount a (FMS→AL xs)
      → FMScount discA a (x ∷ xs) ≡ ALcount a (FMS→AL (x ∷ xs))
   ψ x {xs} p = subst B α θ
    where
    B = λ ys → FMScount discA a (x ∷ xs) ≡ ALcount a ys

    α : ⟨ x , 1 ⟩∷ FMS→AL xs ≡ FMS→AL (x ∷ xs)
    α = sym (multi-∷-id x 1 xs)

    θ : FMScount discA a (x ∷ xs) ≡ ALcount a (⟨ x , 1 ⟩∷ (FMS→AL xs))
    θ = χ x (FMScount discA a xs) (ALcount a (FMS→AL xs)) (discA a x) p



 FMS-with-str≡AL-with-str : FMS-with-str discA ≡ AL-with-str
 FMS-with-str≡AL-with-str = sip (Multi-Set-is-SNS A setA)
                                (FMS-with-str discA) AL-with-str
                                (FMSet≃AssocList , FMS→AL-isIso)
