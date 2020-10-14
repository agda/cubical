{-# OPTIONS --cubical --no-import-sorts  #-}

module SyntheticReals.MorePropAlgebra.Bundles where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Foundations.Logic
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.Utils
open import SyntheticReals.MorePropAlgebra.Structures

-- taken from the cubical standard library and adapted to hProps:
-- Semigroup
-- Monoid
-- Group
-- AbGroup
-- Ring
-- CommRing

record Semigroup : Type (ℓ-suc ℓ) where
  constructor semigroup
  field
    Carrier      : Type ℓ
    _·_          : Carrier → Carrier → Carrier
    is-Semigroup : IsSemigroup _·_

  infixl 7 _·_

  open IsSemigroup is-Semigroup public

record Monoid : Type (ℓ-suc ℓ) where
  constructor monoid
  field
    Carrier   : Type ℓ
    ε         : Carrier
    _·_       : Carrier → Carrier → Carrier
    is-Monoid : IsMonoid ε _·_

  infixl 7 _·_

  open IsMonoid is-Monoid public

record Group : Type (ℓ-suc ℓ) where
  constructor group
  field
    Carrier  : Type ℓ
    0g       : Carrier
    _+_      : Carrier → Carrier → Carrier
    -_       : Carrier → Carrier
    is-Group : IsGroup 0g _+_ -_

  infix  8 -_
  infixr 7 _+_

  open IsGroup is-Group public

record AbGroup : Type (ℓ-suc ℓ) where
  constructor abgroup
  field
    Carrier    : Type ℓ
    0g         : Carrier
    _+_        : Carrier → Carrier → Carrier
    -_         : Carrier → Carrier
    is-AbGroup : IsAbGroup 0g _+_ -_

  infix  8 -_
  infixl 7 _+_

  open IsAbGroup is-AbGroup public

record Ring : Type (ℓ-suc ℓ) where
  constructor ring
  field
    Carrier : Type ℓ
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    is-Ring : IsRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsRing is-Ring public

record CommRing : Type (ℓ-suc ℓ) where
  constructor commring
  field
    Carrier     : Type ℓ
    0r          : Carrier
    1r          : Carrier
    _+_         : Carrier → Carrier → Carrier
    _·_         : Carrier → Carrier → Carrier
    -_          : Carrier → Carrier
    is-CommRing : IsCommRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsCommRing is-CommRing public

record ClassicalField : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _⁻¹     : (x : Carrier) → {{ ! ¬ᵗ(x ≡ 0f) }} → Carrier -- WARNING: we do not have `_⁻¹` as an assuption
    is-ClassicalField : [ isClassicalField 0f 1f _+_ _·_ -_ _⁻¹ ]

  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsClassicalField is-ClassicalField public

record ConstructiveField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor constructivefield
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _#_     : hPropRel Carrier Carrier ℓ'
    is-ConstructiveField : [ isConstructiveField 0f 1f _+_ _·_ -_ _#_ ]

  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_

  open IsConstructiveField is-ConstructiveField public

record Lattice : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor lattice
  field
    Carrier : Type ℓ
    _≤_ : hPropRel Carrier Carrier ℓ'
    min max : Carrier → Carrier → Carrier
    is-Lattice : [ isLattice _≤_ min max ]

  infixl 4 _≤_

  open IsLattice is-Lattice public

record AlmostPartiallyOrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor almostpartiallyorderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
  field
    is-AlmostPartiallyOrderedField : [ isAlmostPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} ] -- defines `_≤_` and `_#_`

  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _<_

  open IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public

record PartiallyOrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor partiallyorderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'

  field
    is-PartiallyOrderedField : [ isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max ] -- defines `_≤_` and `_#_`

  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _<_

  open IsPartiallyOrderedField is-PartiallyOrderedField public

  -- abstract
  --   -- NOTE: there might be some reason not to "do" (or "open") all the theory of a record within that record
  --   +-preserves-< : ∀ a b x → a < b → a + x < b + x
  --   +-preserves-< a b x a<b = (
  --      a            <  b            ⇒⟨ transport (λ i → sym (fst (+-identity a)) i < sym (fst (+-identity b)) i) ⟩
  --      a +    0f    <  b +    0f    ⇒⟨ transport (λ i → a + sym (+-rinv x) i < b + sym (+-rinv x) i) ⟩
  --      a + (x  - x) <  b + (x  - x) ⇒⟨ transport (λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
  --     (a +  x) - x  < (b +  x) - x  ⇒⟨ +-<-extensional (- x) (a + x) (- x) (b + x) ⟩
  --     (a + x < b + x) ⊎ (- x < - x) ⇒⟨ (λ{ (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
  --                                        ; (inr  -x<-x ) → ⊥-elim {A = λ _ → (a + x < b + x)} (<-irrefl (- x) -x<-x) }) ⟩
  --      a + x < b + x ◼) a<b
  --
  --   ≤-isPreorder : IsPreorder _≤_
  --   ≤-isPreorder = ≤-isPreorder' {_<_ = _<_} {<-isStrictPartialOrder}
