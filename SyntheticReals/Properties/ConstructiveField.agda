{-# OPTIONS --cubical --no-import-sorts #-}

open import Bundles

module SyntheticReals.Properties.ConstructiveField {ℓ ℓ'} (F : ConstructiveField {ℓ} {ℓ'}) where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

open import Function.Base using (it) -- instance search

open import MoreLogic
open MoreLogic.Reasoning
import MoreAlgebra

-- Lemma 4.1.6.
-- For a constructive field (F, 0, 1, +, ·, #), the following hold.
-- 1. 1 # 0.
-- 2. Addition + is #-compatible in the sense that for all x, y, z : F
--    x # y ⇔ x + z # y + z.
-- 3. Multiplication · is #-extensional in the sense that for all w, x, y, z : F
--    w · x # y · z ⇒ w # y ∨ x # z.

open ConstructiveField F

open import Cubical.Structures.Ring
R = (makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
open Cubical.Structures.Ring.Theory R
open MoreAlgebra.Properties.Ring R

-- Lemma 4.1.6.1
1f#0f : 1f # 0f
1f#0f with ·-identity 1f
1f#0f | 1·1≡1 , _ = fst (·-inv-back _ _ 1·1≡1)

-- Lemma 4.1.6.2
--   For #-compatibility of +, suppose x # y, that is, (x +z) −z # (y +z) −z.
--   Then #-extensionality gives (x + z # y + z) ∨ (−z # −z), where the latter case is excluded by irreflexivity of #.
+-#-compatible : ∀(x y z : Carrier) → x # y → x + z # y + z
+-#-compatible x y z x#y with
  let P = transport (λ i →  a+b-b≡a x z i # a+b-b≡a y z i ) x#y
  in  +-#-extensional _ _ _ _ P
... | inl x+z#y+z = x+z#y+z
... | inr  -z#-z  = ⊥-elim (#-irrefl _ -z#-z)

-- The other direction is similar.
+-#-compatible-inv : ∀(x y z : Carrier) → x + z # y + z → x # y
+-#-compatible-inv _ _ _ x+z#y+z with +-#-extensional _ _ _ _ x+z#y+z
... | inl x#y = x#y
... | inr z#z = ⊥-elim (#-irrefl _ z#z)

-- Lemma 4.1.6.3
·-#-extensional-case1 : ∀(w x y z : Carrier) → w · x # y · z → w · x # w · z → x # z
·-#-extensional-case1 w x y z w·x#y·z w·x#w·z =
  let
    instance -- this allows to use ⁻¹ᶠ without an instance argument
      w·[z-x]#0f =
        ( w · x         # w ·  z         ⇒⟨ +-#-compatible _ _ (- (w · x)) ⟩
          w · x - w · x # w ·  z - w · x ⇒⟨ transport (λ i →  (fst (+-inv (w · x)) i) # a·b-a·c≡a·[b-c] w z x i) ⟩
                     0f # w · (z - x)    ⇒⟨ #-sym _ _ ⟩
          w ·   (z - x) # 0f             ◼) w·x#w·z
  in  (    w  · (z - x) # 0f                      ⇒⟨ (λ _ → ·-rinv (w · (z - x)) it ) ⟩  -- NOTE: "plugging in" the instance did not work, ∴ `it`
           w  · (z - x) · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-comm w (z - x) i · (w · (z - x)) ⁻¹ᶠ ≡ 1f) ⟩
      (z - x) ·  w      · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-assoc (z - x) w ((w · (z - x)) ⁻¹ᶠ) (~ i) ≡ 1f) ⟩
      (z - x) · (w      · (w · (z - x)) ⁻¹ᶠ) ≡ 1f ⇒⟨ fst ∘ (·-inv-back _ _)  ⟩
         z    - x       # 0f                      ⇒⟨ +-#-compatible _ _ x ⟩
        (z    - x) + x  # 0f + x                  ⇒⟨ transport (λ i → +-assoc z (- x) x (~ i) # snd (+-identity x) i) ⟩
         z + (- x  + x) #      x                  ⇒⟨ transport (λ i → z + snd (+-inv x) i # x) ⟩
         z +      0f    # x                       ⇒⟨ transport (λ i → fst (+-identity z) i # x) ⟩
         z              # x                       ⇒⟨ #-sym _ _ ⟩
         x              # z                       ◼) it -- conceptually we would plug `w·[z-x]#0f` in, but this breaks the very first step


·-#-extensional : ∀(w x y z : Carrier) → w · x # y · z → (w # y) ⊎ (x # z)
·-#-extensional w x y z w·x#y·z with #-cotrans _ _ w·x#y·z (w · z)
... | inl w·x#w·z =    inr (·-#-extensional-case1 w x y z w·x#y·z w·x#w·z) -- first case
... | inr w·z#y·z = let z·w≡z·y = (transport (λ i → ·-comm w z i # ·-comm y z i) w·z#y·z)
                    in inl (·-#-extensional-case1 _ _ _ _ z·w≡z·y z·w≡z·y) -- second case reduced to first case
