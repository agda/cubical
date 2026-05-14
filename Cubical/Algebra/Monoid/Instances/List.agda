module Cubical.Algebra.Monoid.Instances.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Cubical.Algebra.Monoid


ListMonoid : (Σ Type isSet) → Monoid ℓ-zero
fst (ListMonoid (A , _)) = (List A)
MonoidStr.ε (snd (ListMonoid _)) = []
MonoidStr._·_ (snd (ListMonoid _)) = _++_
MonoidStr.isMonoid (snd (ListMonoid (_ , pf))) = makeIsMonoid (isOfHLevelList 0 pf)
                                    (λ x y z → sym (++-assoc x y z)) ++-unit-r (λ _ → refl)

foldlMonHom : (M : Monoid ℓ-zero) → MonoidHom (ListMonoid (fst M , MonoidStr.is-set (snd M))) M
foldlMonHom m = fn , monoidequiv refl respects∙
  where _∙m_ = (MonoidStr._·_ (snd m))
        fn : ⟨ ListMonoid (fst m , MonoidStr.is-set (snd m)) ⟩ → ⟨ m ⟩
        fn xs = foldl (_∙m_) (MonoidStr.ε (snd m)) xs
        ∙foldl : (x y : (fst m)) → (xs : List (fst m)) → x ∙m (foldl _∙m_ y xs) ≡ foldl _∙m_ (x ∙m y) xs
        ∙foldl x y [] = refl
        ∙foldl x y (x₁ ∷ xs) = x ∙m foldl _∙m_ y (x₁ ∷ xs)
                                 ≡⟨ cong (x ∙m_) (sym (∙foldl y x₁ xs)) ⟩
                               x ∙m (y ∙m foldl _∙m_ x₁ xs)
                                 ≡⟨ MonoidStr.·Assoc (snd m) x y (foldl _∙m_ x₁ xs) ⟩
                               (x ∙m y) ∙m foldl _∙m_ x₁ xs
                                 ≡⟨ ∙foldl (x ∙m y) x₁ xs ⟩
                               foldl _∙m_ (x ∙m y) (x₁ ∷ xs) ∎
        fnCons : (x : (fst m)) → (xs : List (fst m)) → x ∙m (fn xs) ≡ (fn (x ∷ xs))
        fnCons x [] = MonoidStr.·IdR (snd m) x ∙ sym (MonoidStr.·IdL (snd m) x)
        fnCons x (x₁ ∷ xs) = x ∙m (fn (x₁ ∷ xs))
                               ≡⟨ cong (x ∙m_) (sym (fnCons x₁ xs)) ⟩
                             (x ∙m (x₁ ∙m fn xs))
                               ≡⟨ MonoidStr.·Assoc (m .snd) x x₁ (fn xs) ⟩
                             ((x ∙m x₁) ∙m fn xs)
                               ≡⟨ ∙foldl (x ∙m  x₁) ((MonoidStr.ε (snd m))) xs ⟩
                             foldl _∙m_ ((x ∙m x₁) ∙m (MonoidStr.ε (snd m))) xs
                               ≡⟨ cong (λ l → foldl _∙m_ l xs) (MonoidStr.·IdR (snd m) (x ∙m x₁)) ⟩
                             foldl _∙m_ x (x₁ ∷ xs)
                               ≡⟨ sym (cong (λ l → foldl _∙m_ l (x₁ ∷ xs)) (MonoidStr.·IdL (snd m) x)) ⟩
                             fn (x ∷ x₁ ∷ xs)  ∎
        respects∙ : (xs ys : List (fst m)) → fn (xs ++ ys) ≡  ((fn xs) ∙m (fn ys))
        respects∙ [] ys = sym (MonoidStr.·IdL (snd m) (fn ys))
        respects∙ xs@(_ ∷ _) [] = cong fn (++-unit-r xs) ∙ sym (MonoidStr.·IdR (snd m) (fn xs))
        respects∙ (x ∷ xs) ys@(_ ∷ _) = fn (x ∷ (xs ++ ys))
                                          ≡⟨ sym (fnCons x (xs ++ ys)) ⟩
                                        x ∙m (fn (xs ++ ys))
                                          ≡⟨ cong (x ∙m_) (respects∙ xs ys) ⟩
                                        x ∙m ((fn xs) ∙m (fn ys))
                                          ≡⟨ MonoidStr.·Assoc (snd m) x (fn xs) (fn ys) ⟩
                                        (x ∙m (fn xs)) ∙m (fn ys)
                                          ≡⟨ cong (_∙m (fn ys)) (fnCons x xs) ⟩
                                        (fn (x ∷ xs)) ∙m (fn ys) ∎
