{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.CountExtensionality where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.HITs.FiniteMultiset.Properties as FMS
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary.DecidableEq


private
 variable
  ℓ : Level


-- We define a partial order on FMSet A and use it to proof
-- a strong induction principle for finite multi-sets.
-- Finally, we use this stronger elimination principle to show
-- that any two FMSets can be identified, if they have the same count for every a : A
module _{A : Type ℓ} (discA : Discrete A) where
 _≼_ : FMSet A → FMSet A → Type ℓ
 xs ≼ ys = ∀ a → FMScount discA a xs ≤ FMScount discA a ys

 ≼-refl : ∀ xs → xs ≼ xs
 ≼-refl xs a  = ≤-refl

 ≼-trans : ∀ xs ys zs → xs ≼ ys → ys ≼ zs → xs ≼ zs
 ≼-trans xs ys zs xs≼ys ys≼zs a = ≤-trans (xs≼ys a) (ys≼zs a)


 ≼[]→≡[] : ∀ xs → xs ≼ [] → xs ≡ []
 ≼[]→≡[] xs xs≼[] = FMScount-0-lemma discA xs λ a → ≤0→≡0 (xs≼[] a)




 ≼-remove1 : ∀ a xs → remove1 discA a xs ≼ xs
 ≼-remove1 a xs b with discA a b
 ...              | yes a≡b = subst (λ n → n ≤ FMScount discA b xs) (sym path) (≤-predℕ)
  where
  path : FMScount discA b (remove1 discA a xs) ≡ predℕ (FMScount discA b xs)
  path = cong (λ c → FMScount discA b (remove1 discA c xs)) a≡b ∙ remove1-predℕ-lemma discA b xs
 ...              | no  a≢b = subst (λ n → n ≤ FMScount discA b xs)
                                    (sym (FMScount-remove1-≢-lemma discA xs λ b≡a → a≢b (sym b≡a))) ≤-refl


 ≼-remove1-lemma : ∀ x xs ys → ys ≼ (x ∷ xs) → (remove1 discA x ys) ≼ xs
 ≼-remove1-lemma x xs ys ys≼x∷xs a with discA a x
 ...                               | yes a≡x = ≤-trans (≤-trans (0 , p₁) (predℕ-≤-predℕ (ys≼x∷xs a)))
                                                                (0 , cong predℕ (FMScount-≡-lemma discA xs a≡x))
  where
  p₁ : FMScount discA a (remove1 discA x ys) ≡ predℕ (FMScount discA a ys)
  p₁ = subst (λ b →  FMScount discA a (remove1 discA b ys) ≡ predℕ (FMScount discA a ys)) a≡x (remove1-predℕ-lemma discA a ys)
 ...                               | no  a≢x = ≤-trans (≤-trans (0 ,  FMScount-remove1-≢-lemma discA ys a≢x) (ys≼x∷xs a))
                                                                (0 , FMScount-≢-lemma discA  xs a≢x)


 ≼-Dichotomy : ∀ x xs ys → ys ≼ (x ∷ xs) → (ys ≼ xs) ⊎ (ys ≡ x ∷ (remove1 discA x ys))
 ≼-Dichotomy x xs ys ys≼x∷xs with (FMScount discA x ys) ≟ suc (FMScount discA x xs)
 ...                         | lt <suc = inl ys≼xs
  where
  ys≼xs : ys ≼ xs
  ys≼xs a with discA a x
  ...     | yes a≡x = pred-≤-pred (subst (λ b → (FMScount discA b ys) < suc (FMScount discA b xs)) (sym a≡x) <suc)
  ...     | no  a≢x = ≤-trans (ys≼x∷xs a) (subst (λ n → FMScount discA a (x ∷ xs) ≤ n) (FMScount-≢-lemma discA xs a≢x) ≤-refl)
 ...                         | eq ≡suc = inr (remove1-suc-lemma discA x (FMScount discA x xs) ys ≡suc)
 ...                         | gt >suc = ⊥.rec (¬m<m strict-ineq)
  where
  strict-ineq : suc (FMScount discA x xs) < suc (FMScount discA x xs)
  strict-ineq =  <≤-trans (<≤-trans >suc (ys≼x∷xs x)) (0 , FMScount-≡-lemma-refl discA xs)



 -- proving a strong elimination principle for finite multisets
 module ≼-ElimProp {ℓ'} {B : FMSet A → Type ℓ'}
                       (BisProp : ∀ {xs} → isProp (B xs)) (b₀ : B [])
                       (B-≼-hyp : ∀ x xs → (∀ ys → ys ≼ xs → B ys) → B (x ∷ xs)) where

  C : FMSet A → Type (ℓ-max ℓ ℓ')
  C xs = ∀ ys → ys ≼ xs → B ys

  g : ∀ xs → C xs
  g = ElimProp.f (isPropΠ2 (λ _ _ → BisProp)) c₀ θ
   where
   c₀ : C []
   c₀ ys ys≼[] = subst B (sym (≼[]→≡[] ys ys≼[])) b₀

   θ : ∀ x {xs} → C xs → C (x ∷ xs)
   θ x {xs} hyp ys ys≼x∷xs with ≼-Dichotomy x xs ys ys≼x∷xs
   ...                     | inl ys≼xs   = hyp ys ys≼xs
   ...                     | inr ys≡x∷zs = subst B (sym ys≡x∷zs) (B-≼-hyp x zs χ)
    where
    zs = remove1 discA x ys
    χ : ∀ vs → vs ≼ zs → B vs
    χ vs vs≼zs = hyp vs (≼-trans vs zs xs vs≼zs (≼-remove1-lemma x xs ys ys≼x∷xs))

  f : ∀ xs → B xs
  f = C→B g
   where
   C→B : (∀ xs → C xs) → (∀ xs → B xs)
   C→B C-hyp xs = C-hyp xs xs (≼-refl xs)


 ≼-ElimPropBin :  ∀ {ℓ'} {B : FMSet A → FMSet A → Type ℓ'}
                   → (∀ {xs} {ys} → isProp (B xs ys))
                   → (B [] [])
                   → (∀ x xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B (x ∷ xs) ys)
                   → (∀ x xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B xs (x ∷ ys))
                   -------------------------------------------------------------------------------
                   → (∀ xs ys → B xs ys)
 ≼-ElimPropBin {B = B} BisProp b₀₀ left-hyp right-hyp = ≼-ElimProp.f (isPropΠ (λ _ → BisProp)) θ χ
  where
  θ : ∀ ys → B [] ys
  θ = ≼-ElimProp.f BisProp b₀₀ h₁
   where
   h₁ : ∀ x ys → (∀ ws → ws ≼ ys → B [] ws) → B [] (x ∷ ys)
   h₁ x ys mini-h = right-hyp x [] ys h₂
    where
    h₂ : ∀ vs ws → vs ≼ [] → ws ≼ ys → B vs ws
    h₂ vs ws vs≼[] ws≼ys = subst (λ zs → B zs ws) (sym (≼[]→≡[] vs vs≼[])) (mini-h ws ws≼ys)

  χ : ∀ x xs → (∀ zs → zs ≼ xs → (∀ ys → B zs ys)) → ∀ ys → B (x ∷ xs) ys
  χ x xs h ys = left-hyp x xs ys λ vs ws vs≼xs _ → h vs vs≼xs ws



 ≼-ElimPropBinSym :  ∀ {ℓ'} {B : FMSet A → FMSet A → Type ℓ'}
                      → (∀ {xs} {ys} → isProp (B xs ys))
                      → (∀ {xs} {ys} → B xs ys → B ys xs)
                      → (B [] [])
                      → (∀ x xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B (x ∷ xs) ys)
                      ----------------------------------------------------------------------------
                      → (∀ xs ys → B xs ys)
 ≼-ElimPropBinSym {B = B} BisProp BisSym b₀₀ left-hyp = ≼-ElimPropBin BisProp b₀₀ left-hyp right-hyp
  where
  right-hyp : ∀ x xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B xs (x ∷ ys)
  right-hyp x xs ys h₁ = BisSym (left-hyp x ys xs (λ vs ws vs≼ys ws≼xs → BisSym (h₁ ws vs ws≼xs vs≼ys)))


 -- The main result
 module FMScountExt where
  B : FMSet A → FMSet A → Type ℓ
  B xs ys = (∀ a → FMScount discA a xs ≡ FMScount discA a ys) → xs ≡ ys

  BisProp : ∀ {xs} {ys} → isProp (B xs ys)
  BisProp = isPropΠ λ _ → trunc _ _

  BisSym : ∀ {xs} {ys} → B xs ys → B ys xs
  BisSym {xs} {ys} b h = sym (b (λ a → sym (h a)))

  b₀₀ : B [] []
  b₀₀ _ = refl

  left-hyp : ∀ x xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B (x ∷ xs) ys
  left-hyp x xs ys hyp h₁ = (λ i → x ∷ (hyp-path i)) ∙ sym path
   where
   eq₁ : FMScount discA x ys ≡ suc (FMScount discA x xs)
   eq₁ = sym (h₁ x) ∙ FMScount-≡-lemma-refl discA xs

   path : ys ≡ x ∷ (remove1 discA x ys)
   path = remove1-suc-lemma discA x (FMScount discA x xs) ys eq₁

   hyp-path : xs ≡ remove1 discA x ys
   hyp-path = hyp xs (remove1 discA x ys) (≼-refl xs) (≼-remove1 x ys) θ
    where
    θ : ∀ a → FMScount discA a xs ≡ FMScount discA a (remove1 discA x ys)
    θ a with discA a x
    ... | yes a≡x = subst (λ b → FMScount discA b xs ≡ FMScount discA b (remove1 discA x ys)) (sym a≡x) eq₂
     where
     eq₂ : FMScount discA x xs ≡ FMScount discA x (remove1 discA x ys)
     eq₂ = FMScount discA x xs                     ≡⟨ cong predℕ (sym (FMScount-≡-lemma-refl discA xs)) ⟩
           predℕ (FMScount discA x (x ∷ xs))       ≡⟨ cong predℕ (h₁ x) ⟩
           predℕ (FMScount discA x ys)             ≡⟨ sym (remove1-predℕ-lemma discA x ys) ⟩
           FMScount discA x (remove1 discA x ys)   ∎
    ... | no  a≢x =
           FMScount discA a xs                         ≡⟨ sym (FMScount-≢-lemma discA  xs a≢x) ⟩
           FMScount discA a (x ∷ xs)                   ≡⟨ h₁ a ⟩
           FMScount discA a ys                         ≡⟨ cong (FMScount discA a) path ⟩
           FMScount discA a (x ∷ (remove1 discA x ys)) ≡⟨ FMScount-≢-lemma discA (remove1 discA x ys) a≢x ⟩
           FMScount discA a (remove1 discA x ys)       ∎


  Thm : ∀ xs ys → (∀ a → FMScount discA a xs ≡ FMScount discA a ys) → xs ≡ ys
  Thm = ≼-ElimPropBinSym BisProp BisSym b₀₀ left-hyp
