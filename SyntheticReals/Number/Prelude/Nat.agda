{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Prelude.Nat where

open import Cubical.Data.Nat.Order public using () renaming
  ( _<_      to _<ⁿᵗ_
  ; <-trans  to <ⁿ-trans -- TODO: use different version
  ; _≟_      to _≟ⁿ_
  ; lt       to ltⁿ
  ; gt       to gtⁿ
  ; eq       to eqⁿ
  ; ¬-<-zero to ¬-<ⁿ-zero
  )
open import Data.Nat public using () renaming
  ( _⊔_    to maxⁿ
  ; _⊓_    to minⁿ
  ; _+_    to _+ⁿ_
  ; _*_    to _·ⁿ_
  ; pred   to predⁿ
  )
open import Cubical.Data.Nat public using (suc; zero; ℕ; HasFromNat) renaming
  ( +-comm      to +ⁿ-comm
  ; +-assoc     to +ⁿ-assoc
  ; *-comm      to ·ⁿ-comm
  ; *-suc       to ·ⁿ-suc
  ; *-assoc     to ·ⁿ-assoc
  ; +-suc       to +ⁿ-suc
  ; *-distribˡ  to ·ⁿ-distribˡ
  ; *-distribʳ  to ·ⁿ-distribʳ
  ; *-identityʳ to ·ⁿ-identityʳ
  ; *-identityˡ to ·ⁿ-identityˡ
  ; snotz       to snotzⁿ
  ; injSuc      to injSucⁿ
  ; isSetℕ      to is-setⁿ
  ; inj-m+      to +ⁿ-preserves-≡ˡ
  ; inj-+m      to +ⁿ-preserves-≡ʳ
  ; inj-sm*     to ·ⁿ-reflects-≡ˡ'
  ; inj-*sm     to ·ⁿ-reflects-≡ʳ'
  )
open import SyntheticReals.Number.Instances.Nat as Nat public using () renaming
  ( bundle         to ℕbundle
  ; _<_            to _<ⁿ_
  ; 0<suc          to 0<ⁿsuc
  ; ·-nullifiesˡ   to ·ⁿ-nullifiesˡ
  ; ·-nullifiesʳ   to ·ⁿ-nullifiesʳ
  ; <-irrefl       to <ⁿ-irrefl
  ; suc-creates-<  to sucⁿ-creates-<ⁿ
  ; <-cotrans      to <ⁿ-cotrans
  ; ¬suc<0         to ¬suc<ⁿ0
  ; ·-reflects-<   to ·ⁿ-reflects-<ⁿ
  ; ·-preserves-<  to ·ⁿ-preserves-<ⁿ
  ; +-createsʳ-<   to +ⁿ-createsʳ-<ⁿ
  ; +-createsˡ-<   to +ⁿ-createsˡ-<ⁿ
  ; min-comm       to minⁿ-comm
  ; min-tightˡ     to minⁿ-tightˡ
  ; min-tightʳ     to minⁿ-tightʳ
  ; min-identity   to minⁿ-identity
  ; max-comm       to maxⁿ-comm
  ; max-tightˡ     to maxⁿ-tightˡ
  ; max-tightʳ     to maxⁿ-tightʳ
  ; max-identity   to maxⁿ-identity
  ; MinTrichtotomy to MinTrichtotomyⁿ
  ; MaxTrichtotomy to MaxTrichtotomyⁿ
  ; min-trichotomy to minⁿ-trichotomy
  ; max-trichotomy to maxⁿ-trichotomy
  ; is-min         to is-minⁿ
  ; is-max         to is-maxⁿ
  ; +-<-ext        to +ⁿ-<ⁿ-ext
  ; ·-reflects-≡ʳ  to ·ⁿ-reflects-≡ʳ
  ; ·-reflects-≡ˡ  to ·ⁿ-reflects-≡ˡ
  )

open import SyntheticReals.MorePropAlgebra.Definitions
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.Number.Structures2

open IsMonoid            Nat.+-Monoid            public using () renaming (is-identity to +ⁿ-identity)
open IsMonoid            Nat.·-Monoid            public using () renaming (is-identity to ·ⁿ-identity)
open IsSemiring          Nat.is-Semiring         public using () renaming (is-dist     to is-distⁿ)
open IsStrictLinearOrder Nat.<-StrictLinearOrder public using () renaming (is-tricho   to is-trichoⁿ)
-- <-StrictLinearOrder .IsStrictLinearOrder.is-trans  a b c = <-trans {a} {b} {c}
