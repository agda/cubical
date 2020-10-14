{-# OPTIONS --cubical --no-import-sorts  #-}


open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_)
import Cubical.Algebra.Group as Std
-- import Cubical.Structures.Group.Properties
open import SyntheticReals.MorePropAlgebra.Bundles

module SyntheticReals.MorePropAlgebra.Properties.Group {ℓ} (assumptions : Group {ℓ}) where
open Group assumptions renaming (Carrier to G)

import SyntheticReals.MorePropAlgebra.Properties.Monoid
module Monoid'Properties = SyntheticReals.MorePropAlgebra.Properties.Monoid   (record { Group assumptions }) -- how does this even work without renaming?
module Monoid'           =                                           Monoid   (record { Group assumptions })
(      Monoid')          =                                           Monoid ∋ (record { Group assumptions })

stdIsGroup : Std.IsGroup 0g _+_ (-_)
stdIsGroup  .Std.IsGroup.isMonoid = Monoid'Properties.stdIsMonoid
stdIsGroup  .Std.IsGroup.inverse  = is-inverse

stdGroup : Std.Group {ℓ}
stdGroup = record { Group assumptions ; isGroup = stdIsGroup }

module GroupLemmas' = Std.GroupLemmas stdGroup

-- module GroupLemmas (G : Group {ℓ}) where
--   open Group G public
--   abstract
--     simplL : (a : Carrier) {b c : Carrier} → a + b ≡ a + c → b ≡ c
--     simplR : {a b : Carrier} (c : Carrier) → a + c ≡ b + c → a ≡ b
--     invInvo : (a : Carrier) → - (- a) ≡ a
--     invId : - 0g ≡ 0g
--     idUniqueL : {e : Carrier} (x : Carrier) → e + x ≡ x → e ≡ 0g
--     idUniqueR : (x : Carrier) {e : Carrier} → x + e ≡ x → e ≡ 0g
--     invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
--     invUniqueR : {g h : Carrier} → g + h ≡ 0g → h ≡ - g
--     invDistr : (a b : Carrier) → - (a + b) ≡ - b - a

-- private
--   simplR = GroupLemmas.simplR G

abstract
  invUniqueL : {g h : G} → g + h ≡ 0g → g ≡ - h
  invUniqueL {g} {h} p = GroupLemmas'.simplR h (p ∙ sym (is-invl h))

  -- ported from `Algebra.Properties.Group`
  private
    right-helper : ∀ x y → y ≡ - x + (x + y)
  right-helper x y = (
    y               ≡⟨ sym (snd (is-identity y)) ⟩
    0g          + y ≡⟨ cong₂ _+_ (sym (snd (is-inverse x))) refl  ⟩
    ((- x) + x) + y ≡⟨ sym (is-assoc (- x) x y) ⟩
    (- x) + (x + y) ∎)

  -- alternative:
  --   follows from uniqueness of -
  --     (a + -a) ≡ 0
  --     ∃! b . a + b = 0
  --   show that a is an additive inverse of - a then it must be THE additive inverse of - a and has to be called - - a which is a by uniqueness
  -involutive : ∀ x → - - x ≡ x
  -involutive x = (
    (- (- x))             ≡⟨ sym (fst (is-identity _)) ⟩
    (- (- x)) + 0g        ≡⟨ cong₂ _+_ refl (sym (snd (is-inverse _))) ⟩
    (- (- x)) + (- x + x) ≡⟨ sym (right-helper (- x) x) ⟩
    x                     ∎)
