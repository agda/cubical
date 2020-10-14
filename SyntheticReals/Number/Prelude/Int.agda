{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Prelude.Int where

open import Cubical.Data.Int public using
  ( Int
  ; fromNatInt
  ; fromNegInt
  ; sucInt
  ; predInt
  ; sucInt+
  ; predInt+
  ; _+pos_
  ; _+negsuc_
  ) renaming
  ( isSetInt to isSetℤ
  ; _-_      to infix 7 _-ᶻ_
  ; _+_      to infix 5 _+ᶻ_
  ; pos      to posᶻ
  ; negsuc   to negsucᶻ
  )
open import SyntheticReals.Number.Instances.Int public using
  ( +negsuc-identityˡ
  ; negsuc+negsuc≡+ⁿ
  ; sneg
  ; spos
  ) renaming
  ( _·_          to _·ᶻ_
  ; -_           to -ᶻ_
  ; _<_          to _<ᶻ_
  ; min          to minᶻ
  ; max          to maxᶻ
  ; is-min       to is-minᶻ
  ; is-max       to is-maxᶻ
  ; ·-reflects-< to ·ᶻ-reflects-<ᶻ
  ; is-LinearlyOrderedCommRing to is-LinearlyOrderedCommRingᶻ
  )

-- Int≅Builtin
-- Int≡Builtin
-- Sign
-- spos
-- sneg
-- _·ˢ_
-- sign
-- signed
-- -_
-- -involutive
-- _·_
-- _·'_
-- _·''_
-- ·''-nullifiesʳ
-- _<_
-- min
-- max
-- <-irrefl
-- <-trans
-- <-asym
-- <-cotrans
-- +-identityʳ
-- +-identityˡ
-- -1·≡-
-- negsuc≡-pos
-- negsuc-reflects-≡
-- pos-reflects-≡
-- possuc+negsuc≡0
-- sucInt[negsuc+pos]≡0
-- +-inverseʳ
-- +-inverseˡ
-- +-inverse
-- pos+pos≡+ⁿ
-- negsuc+negsuc≡+ⁿ
-- +negsuc-identityˡ
-- pos+negsuc≡⊎
-- negsuc+pos≡⊎
-- pos+negsuc≡negsuc+pos
-- predInt-
-- pos+negsuc-swap
-- negsuc+pos-swap
-- +negsuc-assoc
-- sucInt[negsuc+pos]≡pos
-- +pos-inverse
-- +pos-assoc
-- Trichotomy
-- _≟_
-- MinTrichtotomy
-- MaxTrichtotomy
-- min-trichotomy
-- max-trichotomy
-- is-min
-- is-max
-- sucInt-reflects-<
-- predInt-reflects-<
-- sucInt-preserves-<
-- predInt-preserves-<
-- +-preserves-<
-- +-reflects-<
-- +-reflects-<ˡ
-- +-<-ext
-- ·≡·'
-- ·'-nullifiesʳ
-- ·'-nullifiesˡ
-- -distrˡ
-- ·-comm
-- -distrʳ
-- ·'-assoc
-- ·'-assoc≡
-- ·-assoc
-- ·-nullifiesˡ
-- ·-nullifiesʳ
-- ·-identityˡ
-- ·-identityʳ
-- ·-preserves-<
-- ·-reflects-<
-- ·-sucInt
-- ·-sucIntˡ
-- ·-predInt
-- ·-predIntˡ
-- -distrib
-- ·-distribˡ
-- ·-distribʳ

-- ·-Semigroup .IsSemigroup.is-assoc
-- +-Monoid .IsMonoid.is-identity
-- ·-Monoid .IsMonoid.is-identity
-- is-Semiring .IsSemiring.is-dist
-- <-StrictLinearOrder .IsStrictLinearOrder.is-tricho
