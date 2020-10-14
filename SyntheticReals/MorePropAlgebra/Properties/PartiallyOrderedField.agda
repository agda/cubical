{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_; it; typeOf)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax  to infix -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix -4 ∃[∶]-syntax  --
  ; ∀[∶]-syntax to infix -4 ∀[∶]-syntax  --
  ; ∀[]-syntax  to infix -4 ∀[]-syntax   --
  )
-- open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax  to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax  to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax   to infix -4 ∀〚∶〛-syntax
  ; Σᵖ[]-syntax   to infix -4 Σᵖ[]-syntax
  ; Σᵖ[∶]-syntax  to infix -4 Σᵖ[∶]-syntax
  ) hiding (≡ˢ-syntax)
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.MorePropAlgebra.Bundles

module SyntheticReals.MorePropAlgebra.Properties.PartiallyOrderedField {ℓ ℓ'} (assumptions : PartiallyOrderedField {ℓ} {ℓ'})
  (let _≡ˢ_ = λ(x y : PartiallyOrderedField.Carrier assumptions) → SyntheticReals.MoreLogic.Definitions.≡ˢ-syntax x y {PartiallyOrderedField.is-set assumptions}
       infixl 4 _≡ˢ_
  ) where

import SyntheticReals.MorePropAlgebra.Properties.AlmostPartiallyOrderedField
module AlmostPartiallyOrderedField'Properties  = SyntheticReals.MorePropAlgebra.Properties.AlmostPartiallyOrderedField   record { PartiallyOrderedField assumptions }
module AlmostPartiallyOrderedField'            =                                           AlmostPartiallyOrderedField   record { PartiallyOrderedField assumptions }
-- (      AlmostPartiallyOrderedField')           =                            AlmostPartiallyOrderedField ∋ record { PartiallyOrderedField assumptions }

-- open PartiallyOrderedField assumptions renaming (Carrier to F; _-_ to _-_)

import SyntheticReals.MorePropAlgebra.Booij2020
open SyntheticReals.MorePropAlgebra.Booij2020.Chapter4 (record { PartiallyOrderedField assumptions })
open +-<-ext+·-preserves-<⇒ (PartiallyOrderedField.+-<-ext assumptions) (PartiallyOrderedField.·-preserves-< assumptions)
-- open AlmostPartiallyOrderedField'
open SyntheticReals.MorePropAlgebra.Properties.AlmostPartiallyOrderedField (record { PartiallyOrderedField assumptions })
open AlmostPartiallyOrderedField' using (_#_; _≤_)
open PartiallyOrderedField assumptions renaming (Carrier to F; _-_ to _-_) hiding (_#_; _≤_)

abstract
  #-tight : ∀ a b → [ ¬(a # b) ] → a ≡ b; _ : [ isTightˢ''' _#_ is-set ]; _ = #-tight
  #-tight = isTightˢ'''⇔isAntisymˢ _<_ is-set <-asym .snd ≤-antisym

  +-#-ext : ∀ w x y z → [ (w + x) # (y + z) ] → [ (w # y) ⊔ (x # z) ]; _ : [ is-+-#-Extensional _+_ _#_ ]; _ = +-#-ext
  -- Consider the case w + x < y + z, so that we can use (†) to obtain w < y ∨ x < z,
  --   which gives w # y ∨ x # z in either case.
  +-#-ext w x y z (inl w+x<y+z) = case +-<-ext _ _ _ _ w+x<y+z as (w < y) ⊔ (x < z) ⇒ ((w # y) ⊔ (x # z)) of λ
    { (inl w<y) → inlᵖ (inl w<y)
    ; (inr x<z) → inrᵖ (inl x<z) }
  -- The case w + x > y + z is similar.
  +-#-ext w x y z (inr y+z<w+x) = case +-<-ext _ _ _ _ y+z<w+x as (y < w) ⊔ (z < x) ⇒ ((w # y) ⊔ (x # z)) of λ
    { (inl y<w) → inlᵖ (inr y<w)
    ; (inr z<x) → inrᵖ (inr z<x) }

  ¬≤⇒≢ : ∀ x y → [ ¬(x ≤ y) ] → [ ¬(x ≡ˢ y) ]
  ¬≤⇒≢ x y ¬x≤y x≡y = ¬x≤y (subst (λ p → [ x ≤ p ]) x≡y (≤-refl x))

  ≢⇒¬¬# : ∀ x y → [ ¬(x ≡ˢ y) ] → [ ¬ ¬(x # y) ]
  ≢⇒¬¬# x y x≢y = contraposition (¬ (x # y)) (x ≡ˢ y) (#-tight x y) x≢y

  -- x ≤ y → x # y → x < y
  -- x ≤ y ≡ ¬(y ≤ x)
  -- ¬(x # y) → x ≡ y

  ¬≤⇒¬¬# : ∀ x y → [ (¬(x ≤ y)) ⇒ ¬ ¬ (x # y) ]
  ¬≤⇒¬¬# x y ¬x≤y = ≢⇒¬¬# x y $ ¬≤⇒≢ x y ¬x≤y

  ¬≤≡¬¬< : ∀ x y → ¬(x ≤ y) ≡ ¬ ¬ (y < x)
  ¬≤≡¬¬< x y = refl

  min-≤' : ∀ x y → [ (min x y ≤ x) ⊓ (min x y ≤ y) ]
  min-≤' x y = is-min x y (min x y) .fst (≤-refl (min x y))

  ¬¬<-trans : ∀ x y z → [ ¬ ¬ (x < y) ] → [ ¬ ¬ (y < z) ] → [ ¬ ¬ (x < z) ]
  ¬¬<-trans x y z ¬¬x<y ¬¬y<z = ( contraposition (¬ (x < z)) (¬ ((x < y) ⊓ (y < z)))
                                $ contraposition ((x < y) ⊓ (y < z)) (x < z)
                                $ uncurryₚ (x < y) (y < z) (x < z) (<-trans x y z)
                                ) (⊓¬¬⇒¬¬⊓ (x < y) (y < z) ¬¬x<y ¬¬y<z)

  ¬¬<-irrefl : ∀ x → [ ¬ ¬ ¬(x < x) ]
  ¬¬<-irrefl x = ¬¬-intro (¬(x < x)) (<-irrefl x)

  -- lem : ∀ (x y z : F) → {!   !}
  -- lem x y z = let f : [ x < y ] → [ (x < z) ⊔ (z < y) ]
  --                 f p = <-cotrans x y p z -- contraposition ((z ≤ x) ⊓ (y ≤ z)) (y ≤ x) $
  --                 _ = {!    !}
  --             in {! contraposition (x < y) ((x < z) ⊔ (z < y)) f ∘ deMorgan₂-back (x < z) (z < y)  !}

  -- foo : ∀(x y z w : F) → [ w < min (x · z) (y · z) ] → [ w < min x y · z ]
  -- foo x y z w = {! <-cotrans w (min x y) ? x   !}

  -- foo : ∀(x y z w : F) → [ w < min (x · z) (y · z) ] → [ w < min x y · z ]


  min-<-⊔ : ∀ x y z → [ min x y < z ] → [ (x < z) ⊔ (y < z) ]
  min-<-⊔ x y z mxy<z = case <-cotrans (min x y) z mxy<z x as (min x y < x) ⊔ (x < z) ⇒ (x < z) ⊔ (y < z) of λ
    { (inl p) → case <-cotrans (min x y) z mxy<z y as (min x y < y) ⊔ (y < z) ⇒ (x < z) ⊔ (y < z) of λ
      { (inl q) → -- We know that
                  --   x ≤ min(x, y) ⇔ x ≤ x ∧ x ≤ y,
                  --   y ≤ min(x, y) ⇔ y ≤ x ∧ y ≤ y.
                  -- By the fact that min(x, y) < x and min(x, y) < y, the left hand sides of these claims are false,
                  -- and hence we have ¬(x ≤ y) and ¬(y ≤ x), which together contradict that < is transitive and
                  -- irreflexive.
                  let (mxy≤x , mxy≤y) = is-min x y (min x y) .fst (<-irrefl (min x y))
                      r = contraposition ((x ≤ x) ⊓ (x ≤ y)) (¬ (min x y < x)) (is-min x y x .snd) (¬¬-intro (min x y < x) p)
                      ¬x≤y = implication (x ≤ x) (x ≤ y) r (≤-refl x)
                      s = contraposition ((y ≤ x) ⊓ (y ≤ y)) (¬ (min x y < y)) (is-min x y y .snd) (¬¬-intro (min x y < y) q)
                      ¬y≤x = ¬-⊓-distrib (y ≤ x) (y ≤ y) s .snd (≤-refl y)
                  in  ⊥-elim {A = λ _ → [ (x < z) ⊔ (y < z) ]} $ ¬¬<-irrefl x (¬¬<-trans x y x ¬y≤x ¬x≤y)
      ; (inr q) → inrᵖ q
      }
    ; (inr p) → inlᵖ p
    }

  -- is this provable?
  -- min-≤-⊔ : ∀ x y z → [ min x y ≤ z ] → [ (x ≤ z) ⊔ (y ≤ z) ]
  -- min-≤-⊔ x y z mxy≤z = {!   !}


  -- lem : ∀ w x y z → [ w ≤ (x + z) ] → [ w ≤ (y + z) ] → [ w ≤ (min x y + z) ]
  -- lem w x y z w≤x+z w≤y+z mxy+z<w = {! +-<-ext (min x y) z 0f w  !}

-- Properties.PartiallyOrderedField assumptions
--   opens PartiallyOrderedField assumptions
--     opens IsPartiallyOrderedField is-PartiallyOrderedField public
--       opens IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public
--         contains definition of _#_
--           becomes `_#_`
--   opens MorePropAlgebra.Properties.AlmostPartiallyOrderedField assumptions
--     opens AlmostPartiallyOrderedField assumptions
--       opens IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public
--         contains definition of _#_
--           becomes `AlmostPartiallyOrderedField'._#_`

-- all these become `_#_`
--   _#_
--   PartiallyOrderedField._#_ assumptions
--   IsPartiallyOrderedField._#_ (PartiallyOrderedField.is-PartiallyOrderedField assumptions)
--   IsAlmostPartiallyOrderedField._#_ (IsPartiallyOrderedField.is-AlmostPartiallyOrderedField (PartiallyOrderedField.is-PartiallyOrderedField assumptions))
-- but
--   PartiallyOrderedField._#_ (record { PartiallyOrderedField assumptions })
-- becomes
--   PartiallyOrderedField._#_ record { Carrier = F ; 0f = 0f ; 1f = 1f ; _+_ = _+_ ; -_ = -_ ; _·_ = _·_ ; min = min ; max = max ; _<_ = _<_ ; is-PartiallyOrderedField = is-PartiallyOrderedField }
-- when we define
--   foo = PartiallyOrderedField ∋ (record { PartiallyOrderedField assumptions })
-- then
--   PartiallyOrderedField._#_ foo
-- becomes
--   (foo PartiallyOrderedField.# x)

-- foo = PartiallyOrderedField ∋ (record { PartiallyOrderedField assumptions })
--
-- test : ∀ x y → [ (PartiallyOrderedField._#_ foo) x y ]
-- test = {! ·-inv''  !}
