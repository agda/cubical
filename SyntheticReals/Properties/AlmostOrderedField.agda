{-# OPTIONS --cubical --no-import-sorts #-}

open import Bundles

module SyntheticReals.Properties.AlmostOrderedField {ℓ ℓ'} (AOF : AlmostOrderedField {ℓ} {ℓ'}) where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

open import Function.Base using (_∋_)
open import Function.Base using (it) -- instance search

import MoreLogic
open MoreLogic.Reasoning
import MoreAlgebra

-- Lemma 4.1.11.
-- In the presence of the first five axioms of Definition 4.1.10, conditions (†) and (∗) are together equivalent to the condition that for all x, y, z : F,
--  1. x ≤ y ⇔ ¬(y < x),
--  2. x # y ⇔ (x < y) ∨ (y < x)
--  3. x ≤ y ⇔ x + z ≤ y + z,
--  4. x < y ⇔ x + z < y + z,
--  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
--  6. x < y ≤ z ⇒ x < z,
--  7. x ≤ y < z ⇒ x < z,
--  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
--  9. 0 < z ⇒ (x < y ⇔ x z < y z),
-- 10. 0 < 1.

open AlmostOrderedField AOF renaming (Carrier to F)
import Cubical.Structures.Ring
open Cubical.Structures.Ring.Theory (record {AlmostOrderedField AOF})
open MoreAlgebra.Properties.Group   (record {AlmostOrderedField AOF renaming (+-isGroup to isGroup )})


-- NOTE: ported from Cubical.Structures.Group.GroupLemmas
-- NOTE: these versions differ from the Group-versions because they are defined w.r.t. an appartness relation _#_ that is not present for the Group
simplR : {a b : F} (c : F) {{_ : c # 0f}} → a · c ≡ b · c → a ≡ b
simplR {a} {b} c {{_}} a·c≡b·c =
   a                ≡⟨ sym (fst (·-identity a)) ∙ cong (a ·_) (sym (·-rinv c it)) ∙ ·-assoc _ _ _ ⟩
  (a · c) · (c ⁻¹ᶠ) ≡⟨ cong (_· c ⁻¹ᶠ) a·c≡b·c ⟩
  (b · c) · (c ⁻¹ᶠ) ≡⟨ sym (·-assoc _ _ _) ∙ cong (b ·_) (·-rinv c it) ∙ fst (·-identity b)  ⟩
   b ∎

·-preserves-≡ʳ : {a b : F} (c : F) {{_ : c # 0f}} → a · c ≡ b · c → a ≡ b
·-preserves-≡ʳ = simplR

-- ·-linv-unique : (x y : F) (x·y≡1 : (x ·₁ y) ≡ 1f) → x ≡ (y ⁻¹ᶠ₁)
module _ (x y : F) (x·y≡1 : x · y ≡ 1f) where
  y#0 = snd (·-inv-back _ _ x·y≡1) -- duplicated inhabitant (see notes)
  instance _ = y # 0f ∋ y#0
  import Cubical.Structures.Group

  -- NOTE: ported from Cubical.Structures.Group.GroupLemmas
  abstract
    ·-linv-unique' : Σ[ p ∈ y # 0f ] (x ≡ _⁻¹ᶠ y {{p}})
    ·-linv-unique' = it , (
      x · y ≡ 1f        ⇒⟨ transport (λ i → x · y ≡ ·-linv y it (~ i)) ⟩
      x · y ≡ y ⁻¹ᶠ · y ⇒⟨ simplR _  ⟩
      x     ≡ y ⁻¹ᶠ     ◼) x·y≡1

·-linv-unique : (x y : F) → ((x · y) ≡ 1f) → Σ[ p ∈ y # 0f ] x ≡ (_⁻¹ᶠ y {{p}})
·-linv-unique = ·-linv-unique'

-- ⁻¹ᶠ-involutive : (x : F) (z#0 : x #' 0f) → ((x ⁻¹ᶠ₁) ⁻¹ᶠ₁) ≡ x
module _ (z : F) (z#0 : z # 0f) where
  private
    instance _ = z#0
    z⁻¹ = z ⁻¹ᶠ -- NOTE: interestingly, the instance argument is not applied and y remains normalized in terms of z
              --       so we get `y : {{ _ : z #' 0f }} → F` here
    z⁻¹#0 = snd (·-inv-back z z⁻¹ (·-rinv z it))
    -- NOTE: for some reason I get "There are instances whose type is still unsolved when checking that the expression it has type z #' 0f"
    --       typing `y : F` did not help much. therefore this goes in two lines
    instance _ = z⁻¹#0
    z⁻¹⁻¹ = z⁻¹ ⁻¹ᶠ

  -- NOTE: this should be similar to `right-helper` + `-involutive`
  ⁻¹ᶠ-involutive : (z ⁻¹ᶠ) ⁻¹ᶠ ≡ z
  ⁻¹ᶠ-involutive = (
     z⁻¹⁻¹              ≡⟨ sym (fst (·-identity _)) ⟩
     z⁻¹⁻¹ ·      1f    ≡⟨ (λ i →  z⁻¹⁻¹ · ·-linv _ it (~ i)) ⟩
     z⁻¹⁻¹ · (z⁻¹  · z) ≡⟨ ·-assoc _ _ _ ⟩
    (z⁻¹⁻¹ ·  z⁻¹) · z  ≡⟨ (λ i → ·-linv z⁻¹ it i · z) ⟩
          1f       · z  ≡⟨  snd (·-identity _)  ⟩
                     z  ∎)

module forward -- 6. ⇒ 1. 2. 3. 4. 5.
  -- 6. (†)
  (+-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w))
  -- 6. (∗)
  (·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z))
  where
  -- abstract
    --  1. x ≤ y ⇔ ¬(y < x),
    item-1 : ∀ x y → x ≤ y → ¬(y < x)
    item-1 = λ _ _ x≤y → x≤y -- holds definitionally

    item-1-back : ∀ x y → ¬(y < x) → x ≤ y
    item-1-back = λ _ _ ¬[y<x] → ¬[y<x]

    --  2. x # y ⇔ (x < y) ∨ (y < x)
    item-2 : ∀ x y → x # y → (x < y) ⊎ (y < x)
    item-2 = λ _ _ x#y → x#y -- holds definitionally

    item-2-back : ∀ x y → (x < y) ⊎ (y < x) → x # y
    item-2-back = λ _ _ [x<y]⊎[y<x] → [x<y]⊎[y<x] -- holds definitionally

    -- NOTE: just a plain copy of the previous proof
    +-preserves-< : ∀ a b x → a < b → a + x < b + x
    +-preserves-< a b x a<b = (
       a            <  b            ⇒⟨ transport (λ i → sym (fst (+-identity a)) i < sym (fst (+-identity b)) i) ⟩
       a +    0f    <  b +    0f    ⇒⟨ transport (λ i → a + sym (+-rinv x) i < b + sym (+-rinv x) i) ⟩
       a + (x  - x) <  b + (x  - x) ⇒⟨ transport (λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
      (a +  x) - x  < (b +  x) - x  ⇒⟨ +-<-extensional (- x) (a + x) (- x) (b + x) ⟩
      (a + x < b + x) ⊎ (- x < - x) ⇒⟨ (λ{ (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                         ; (inr  -x<-x ) → ⊥-elim {A = λ _ → (a + x < b + x)} (<-irrefl (- x) -x<-x) }) ⟩
       a + x < b + x ◼) a<b

    +-preserves-<-back : ∀ x y z → x + z < y + z → x < y
    +-preserves-<-back x y z =
      ( x + z < y + z              ⇒⟨ +-preserves-< _ _ (- z) ⟩
        (x + z) - z  < (y + z) - z ⇒⟨ transport (λ i → +-assoc x z (- z) (~ i) < +-assoc y z (- z) (~ i)) ⟩
        x + (z - z) < y + (z - z)  ⇒⟨ transport (λ i → x + +-rinv z i < y + +-rinv z i) ⟩
        x + 0f < y + 0f            ⇒⟨ transport (λ i → fst (+-identity x) i < fst (+-identity y) i) ⟩
        x < y ◼)

    --  3. x ≤ y ⇔ x + z ≤ y + z,
    item-3 : ∀ x y z → x ≤ y → x + z ≤ y + z
    item-3 x y z = (
       x     ≤ y          ⇒⟨ (λ z → z) ⟩ -- unfold the definition
      (y     < x     → ⊥) ⇒⟨ (λ f → f ∘ (+-preserves-<-back y x z) ) ⟩
      (y + z < x + z → ⊥) ⇒⟨ (λ z → z) ⟩ -- refold the definition
       x + z ≤ y + z ◼)

    item-3-back : ∀ x y z → x + z ≤ y + z → x ≤ y
    item-3-back x y z = (
       x + z ≤ y + z      ⇒⟨ (λ z → z) ⟩ -- unfold the definition
      (y + z < x + z → ⊥) ⇒⟨ (λ f p → f (+-preserves-< y x z p)) ⟩ -- just a variant of the above
      (y     < x     → ⊥) ⇒⟨ (λ z → z) ⟩ -- refold the definition
       x     ≤ y ◼)

    --  4. x < y ⇔ x + z < y + z,
    item-4 : ∀ x y z → x < y → x + z < y + z
    item-4 = +-preserves-<

    item-4-back : ∀ x y z → x + z < y + z → x < y
    item-4-back = +-preserves-<-back

    --  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
    item-5 : ∀ x y → 0f < x + y → (0f < x) ⊎ (0f < y)
    item-5 x y = (
      (0f      < x + y) ⇒⟨ transport (λ i → fst (+-identity 0f) (~ i) < x + y) ⟩
      (0f + 0f < x + y) ⇒⟨ +-<-extensional y 0f 0f x ⟩
      (0f < x) ⊎ (0f < y) ◼)

    --  6. x < y ≤ z ⇒ x < z,
    item-6 : ∀ x y z → x < y → y ≤ z → x < z
    item-6 x y z x<y y≤z = (
       x      <  y      ⇒⟨ +-preserves-< _ _ _ ⟩
       x + z  <  y + z  ⇒⟨ transport (λ i → x + z < +-comm y z i) ⟩
       x + z  <  z + y  ⇒⟨ +-<-extensional y x z z  ⟩
      (x < z) ⊎ (z < y) ⇒⟨ (λ{ (inl x<z) → x<z
                             ; (inr z<y) → ⊥-elim (y≤z z<y) }) ⟩
       x < z  ◼) x<y

    --  7. x ≤ y < z ⇒ x < z,
    item-7 : ∀ x y z → x ≤ y → y < z → x < z
    item-7 x y z x≤y = ( -- very similar to the previous one
       y      <  z      ⇒⟨ +-preserves-< y z x ⟩
       y + x  <  z + x  ⇒⟨ transport (λ i → +-comm y x i < z + x) ⟩
       x + y  <  z + x  ⇒⟨ +-<-extensional x x y z ⟩
      (x < z) ⊎ (y < x) ⇒⟨ (λ{ (inl x<z) → x<z
                             ; (inr y<x) → ⊥-elim (x≤y y<x)}) ⟩
       x < z  ◼)

    item-10 : 0f < 1f

    module _ (z : F) (0<z : 0f < z) where
      private
        instance _ = z # 0f ∋ inr 0<z
        z⁻¹ = z ⁻¹ᶠ
        z⁻¹#0 = snd (·-inv-back z z⁻¹ (·-rinv z it))
      abstract
        ⁻¹ᶠ-preserves-sign : 0f < z ⁻¹ᶠ
        ⁻¹ᶠ-preserves-sign with z⁻¹#0
        ... | inl z⁻¹<0 = (
          z⁻¹     < 0f     ⇒⟨ ·-preserves-< _ _ z 0<z ⟩
          z⁻¹ · z < 0f · z ⇒⟨ transport (λ i → ·-linv z it i <  0-leftNullifies z i) ⟩
          1f      < 0f     ⇒⟨ <-trans _ _ _ item-10 ⟩
          0f      < 0f     ⇒⟨ <-irrefl _ ⟩
                  ⊥        ⇒⟨ ⊥-elim ⟩ _ ◼) z⁻¹<0
        ... | inr 0<z⁻¹ = 0<z⁻¹

    --  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
    item-8 : ∀ x y z → x ≤ y → 0f ≤ z → x · z ≤ y · z
    -- For item 8, suppose x ≤ y and 0 ≤ z and yz < xz.
    item-8 x y z x≤y 0≤z y·z<x·z = let
      -- Then 0 < z (x − y) by (†),
      i   = (  y · z            <  x · z                ⇒⟨ transport (λ i → ·-comm y z i < ·-comm x z i) ⟩
               z · y            <  z · x                ⇒⟨ +-preserves-< _ _ _ ⟩
              (z · y) - (z · y) < (z · x) - (z ·    y ) ⇒⟨ transport (cong₂ _<_ (+-rinv (z · y))
                                                             ( λ i → (z · x) + sym (-commutesWithRight-· z y) i )) ⟩
                             0f < (z · x) + (z · (- y)) ⇒⟨ transport (cong₂ _<_ refl (sym (fst (dist z x (- y))))) ⟩ -- [XX]
                             0f <  z · (x - y) ◼) y·z<x·z
      instance _ = z · (x - y) # 0f ∋ inr i
      -- and so, being apart from 0, z (x − y) has a multiplicative inverse w.
      w   = (z · (x - y)) ⁻¹ᶠ
      ii  : 1f ≡ (z · (x - y)) · w
      ii  = sym (·-rinv _ _)
      -- Hence z itself has a multiplicative inverse w (x − y),
      iii : 1f ≡ z · ((x - y) · w)
      iii = transport (λ i → 1f ≡ ·-assoc z (x - y) w (~ i)) ii
      instance z#0f = z # 0f ∋ fst (·-inv-back _ _ (sym iii))
      -- and so 0 < z ∨ z < 0, where the latter case contradicts the assumption 0 ≤ z, so that we have 0 < z.
      instance _    = 0f < z ∋ case z#0f of λ where
                      (inl z<0) → ⊥-elim (0≤z z<0)
                      (inr 0<z) → 0<z
      -- Now w (x − y) has multiplicative inverse z, so it is apart from 0,
      iv  :  (x - y) · w # 0f
      iv  = snd (·-inv-back _ _ (sym iii))
      -- that is (0 < w (x − y)) ∨ (w (x − y) < 0).
      in case iv of λ where
        -- By (∗), from 0 < w (x − y) and yz < xz we get yzw (x − y) < xzw (x − y), so y < x, contradicting our assumption that x ≤ y.
        (inr 0<[x-y]·w) → (
           y ·  z                   <  x ·  z                    ⇒⟨ ·-preserves-< _ _ _ 0<[x-y]·w ⟩
          (y ·  z) · ((x - y) · w)  < (x ·  z) · ((x - y) · w)   ⇒⟨ transport (λ i →
                                                                        (·-assoc y z ((x - y) · w)) (~ i)
                                                                      < (·-assoc x z ((x - y) · w)) (~ i)) ⟩
           y · (z  · ((x - y) · w)) <  x · (z  · ((x - y) · w))  ⇒⟨ transport (λ i →
                                                                       y · (iii (~ i)) < x · (iii (~ i))) ⟩
           y · 1f                   <  x · 1f                    ⇒⟨ transport (cong₂ _<_
                                                                      (fst (·-identity y)) (fst (·-identity x))) ⟩
           y                        <  x                         ⇒⟨ x≤y ⟩
          ⊥ ◼) y·z<x·z
        -- In the latter case, from (∗) we get zw (x − y) < 0, i.e.
        -- 1 < 0 which contradicts item 10, so that we have 0 < w (x − y).
        (inl p) → (
               (x - y) · w      < 0f     ⇒⟨ ·-preserves-< _ _ _ it ⟩
              ((x - y) · w) · z < 0f · z ⇒⟨ transport (cong₂ _<_ (·-comm _ _) (0-leftNullifies z)) ⟩
          z · ((x - y) · w)     < 0f     ⇒⟨ ( transport λ i → iii (~ i) < 0f) ⟩
                             1f < 0f     ⇒⟨ <-trans _ _ _  item-10 ⟩
                             0f < 0f     ⇒⟨ <-irrefl _ ⟩
          ⊥ ◼) p

    --  9. 0 < z ⇒ (x < y ⇔ x z < y z),
    item-9 : ∀ x y z → 0f < z → (x < y → x · z < y · z)
    item-9 = ·-preserves-<

    item-9-back : ∀ x y z → 0f < z → (x · z < y · z → x < y)
    -- For the other direction of item 9, assume 0 < z and xz < yz,
    item-9-back x y z 0<z x·z<y·z = let
      instance _ = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
                   (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                  0f < (y · z) - (x · z) ◼) x·z<y·z
               _ = (y · z) - (x · z) # 0f ∋ inr it
      -- so that yz − xz has a multiplicative inverse w,
      w = ((y · z) - (x · z)) ⁻¹ᶠ
      o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
            (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
            (y - x) · z ∎)
      instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
      -- and so z itself has multiplicative inverse w (y − x).
      1≡z·[w·[y-x]] = γ
      iii = 1≡z·[w·[y-x]]
      1≡[w·[y-x]]·z : 1f ≡ (w · (y - x)) · z
      1≡[w·[y-x]]·z = transport (λ i → 1f ≡ ·-comm z (w · (y - x)) i) 1≡z·[w·[y-x]]
      -- Then since 0 < z and xz < yz, by (∗), we get xzw (y − x) < yzw (y − x), and hence x < y.
      instance _ = z # 0f ∋ inr 0<z
      z⁻¹ = w · (y - x)
      z⁻¹≡w·[y-x] : z ⁻¹ᶠ ≡ (w · (y - x))
      z⁻¹≡w·[y-x] = let tmp = sym (snd (·-linv-unique (w · (y - x)) z (sym 1≡[w·[y-x]]·z)))
                    in transport (cong (λ z#0 → _⁻¹ᶠ z {{z#0}} ≡ (w · (y - x))) (#-isProp z 0f _ _)) tmp
      0<z⁻¹ : 0f < z ⁻¹ᶠ
      0<z⁻¹ = ⁻¹ᶠ-preserves-sign z 0<z
      instance _ = 0f < w · (y - x) ∋ transport (λ i → 0f < z⁻¹≡w·[y-x] i) 0<z⁻¹
      -- instance _ = 0f < z⁻¹ ∋ ?
      in (  x ·  z         <  y ·  z         ⇒⟨ ·-preserves-< _ _ z⁻¹ it ⟩
           (x ·  z) · z⁻¹  < (y ·  z) · z⁻¹  ⇒⟨ transport (λ i → ·-assoc x z z⁻¹ (~ i) < ·-assoc y z z⁻¹ (~ i)) ⟩
            x · (z  · z⁻¹) <  y · (z  · z⁻¹) ⇒⟨ transport (λ i → x · iii (~ i) < y · iii (~ i)) ⟩
            x · 1f         <  y · 1f         ⇒⟨ transport (cong₂ _<_ (fst (·-identity x)) (fst (·-identity y))) ⟩
            x              <  y              ◼) x·z<y·z
      where
        abstract -- NOTE: `abstract` is only allowed in `where` blocks and `where` blocks are not allowed in `let` blocks
          γ =
            let -- NOTE: for some reason the instance resolution does only work in let-blocks
            -- I get a "Terms marked as eligible for instance search should end with a name, so `instance' is ignored here. when checking the definition of my-instance"
            instance my-instance = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
                         (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                        0f < (y · z) - (x · z) ◼) x·z<y·z
                     _ = (y · z) - (x · z) # 0f ∋ inr it
            -- so that yz − xz has a multiplicative inverse w,
            w = ((y · z) - (x · z)) ⁻¹ᶠ
            o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
                  (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
                  (y - x) · z ∎)
            instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
            in (
              1f                      ≡⟨ (λ i → ·-linv ((y · z) - (x · z)) it (~ i)) ⟩
              w · ((y · z) - (x · z)) ≡⟨ (λ i → w · o i) ⟩
              w · ((y - x) · z)       ≡⟨ (λ i → w · ·-comm (y - x) z i ) ⟩
              w · (z · (y - x))       ≡⟨ (λ i → ·-assoc w z (y - x) i) ⟩
              (w · z) · (y - x)       ≡⟨ (λ i → ·-comm w z i · (y - x)) ⟩
              (z · w) · (y - x)       ≡⟨ (λ i → ·-assoc z w (y - x) (~ i)) ⟩
              z · (w · (y - x))       ∎)

    -- 10. 0 < 1.
    item-10 with snd (·-inv-back _ _ (fst (·-identity 1f)))
    -- For item 10, since 1 has multiplicative inverse 1, it is apart from 0, hence 0 < 1 ∨ 1 < 0.
    ... | inl 1<0 =
      -- If 1 < 0 then by item 4 we have 0 < −1 and so by (∗) we get 0 < (−1) · (−1), that is, 0 < 1, so by transitivity 1 < 1, contradicting irreflexivity of <.
       (1f          < 0f                ⇒⟨ +-preserves-< 1f 0f (- 1f) ⟩
        1f    - 1f  < 0f - 1f           ⇒⟨ transport (λ i → +-rinv 1f i < snd (+-identity (- 1f)) i) ⟩
        0f          <    - 1f           ⇒⟨ ( λ 0<-1 → ·-preserves-< 0f (- 1f) (- 1f) 0<-1 0<-1) ⟩
        0f · (- 1f) <   (- 1f) · (- 1f) ⇒⟨ transport (cong₂ _<_ (0-leftNullifies (- 1f)) refl) ⟩
        0f          <   (- 1f) · (- 1f) ⇒⟨ transport (λ i → 0f < -commutesWithRight-· (- 1f) (1f)   i ) ⟩
        0f          < -((- 1f) ·    1f )⇒⟨ transport (λ i → 0f < -commutesWithLeft-·  (- 1f)  1f (~ i)) ⟩
        0f          < (-(- 1f))·    1f  ⇒⟨ transport (λ i → 0f < -involutive 1f i · 1f) ⟩
        0f          <      1f  ·    1f  ⇒⟨ transport (λ i → 0f < fst (·-identity 1f) i) ⟩
        0f          <      1f           ⇒⟨ <-trans _ _ _ 1<0 ⟩
        1f          <      1f           ⇒⟨ <-irrefl 1f ⟩
                    ⊥                   ⇒⟨ ⊥-elim ⟩ _ ◼) 1<0
    ... | inr 0<1 = 0<1

-- Conversely, assume the 10 listed items—in particular, items 4, 5 and 9.
module back -- 1. 2. 3. 4. 5. ⇒ 6.
  -- (item-1      : ∀ x y → x ≤ y → ¬(y < x))
  -- (item-1-back : ∀ x y → ¬(y < x) → x ≤ y)
  -- (item-2      : ∀ x y → x # y → (x < y) ⊎ (y < x))
  -- (item-2-back : ∀ x y → (x < y) ⊎ (y < x) → x # y)
  -- (item-3      : ∀ x y z → x ≤ y → x + z ≤ y + z)
  -- (item-3-back : ∀ x y z → x + z ≤ y + z → x ≤ y)
     (item-4      : ∀ x y z → x < y → x + z < y + z)
  -- (item-4-back : ∀ x y z → x + z < y + z → x < y)
     (item-5      : ∀ x y → 0f < x + y → (0f < x) ⊎ (0f < y))
  -- (item-6      : ∀ x y z → x < y → y ≤ z → x < z)
  -- (item-7      : ∀ x y z → x ≤ y → y < z → x < z)
  -- (item-8      : ∀ x y z → x ≤ y → 0f ≤ z → x · z ≤ y · z)
     (item-9      : ∀ x y z → 0f < z → (x < y → x · z < y · z))
  -- (item-9-back : ∀ x y z → 0f < z → (x · z < y · z → x < y))
  -- (item-10     : 0f < 1f)
  where

  item-4' : ∀ x y → 0f < x - y → y < x
  item-4' x y = (
    0f     <  x - y         ⇒⟨ item-4 0f (x + (- y)) y ⟩
    0f + y < (x - y) + y    ⇒⟨ transport (λ i → snd (+-identity y) i < sym (+-assoc x (- y) y) i) ⟩
         y <  x + (- y + y) ⇒⟨ transport (λ i → y < x + snd (+-inv y) i) ⟩
         y <  x + 0f        ⇒⟨ transport (λ i → y < fst (+-identity x) i)  ⟩
         y <  x ◼)

  lemma : ∀ x y z w → (z +   w) + ((- x)  + (- y)) ≡ (z - x) + (w - y)
  lemma x y z w = (
    -- NOTE: there has to be a shorter way to to this kind of calculations ...
    --       also I got not much introspection while creating the paths
    (z +   w) + ((- x)  + (- y))   ≡⟨ ( λ i → +-assoc z w ((- x)  + (- y)) (~ i)) ⟩
    (z + ( w  + ((- x)  + (- y)))) ≡⟨ ( λ i → z + (+-assoc w (- x) (- y) i)) ⟩
    (z + ((w  +  (- x)) + (- y)))  ≡⟨ ( λ i → z + ((+-comm w (- x) i) + (- y)) ) ⟩
    (z + (((- x) +  w)  + (- y)))  ≡⟨ ( λ i → z + (+-assoc (- x) w (- y) (~ i))) ⟩
    (z + (( - x) + (w - y)))       ≡⟨ ( λ i → +-assoc z (- x) (w  - y) i ) ⟩
    (z - x) + (w - y) ∎)

  -- 6. (†)
  -- In order to show (†), suppose x + y < z + w.
  -- So, by item 4, we get (x + y) − (x + y) < (z + w) − (x + y), that is, 0 < (z − x) + (w − y).
  -- By item 5, (0 < z − x) ∨ (0 < w − y), and so by item 4 in either case, we get x < z ∨ y < w.
  +-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
  +-<-extensional w x y z = (
    (x + y)           < (z + w)           ⇒⟨ item-4 (x + y) (z + w) (- (x + y)) ⟩
    (x + y) - (x + y) < (z + w) - (x + y)
      ⇒⟨ transport (λ i → +-rinv (x + y) i < (z + w) + (-isDistributive x y) (~ i))    ⟩

                   0f < (z +   w) + ((- x)  + (- y))   ⇒⟨ transport (λ i → 0f < lemma x y z w i) ⟩
                   0f < (z - x) + (w - y) ⇒⟨ item-5 (z - x) (w - y) ⟩
    (0f < z - x) ⊎ (0f < w - y)           ⇒⟨ (λ{ (inl p) → inl (item-4' z x p)
                                               ; (inr p) → inr (item-4' w y p)}) ⟩
    ( x < z    ) ⊎ ( y < w    ) ◼)

  -- 6. (∗)
  ·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z)
  ·-preserves-< = item-9
