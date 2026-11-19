module Cubical.Algebra.ArchimedeanField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.PropertiesWithRationals

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

private
  variable
    ℓ ℓ' : Level

ArchimedeanField→StrictOrder : ArchimedeanField ℓ ℓ' → StrictOrder ℓ ℓ'
ArchimedeanField→StrictOrder = OrderedField→StrictOrder ∘ ArchimedeanField→OrderedField

ArchimedeanField→PseudoLattice : ArchimedeanField ℓ ℓ' → Pseudolattice ℓ ℓ'
ArchimedeanField→PseudoLattice =
  OrderedField→PseudoLattice ∘ ArchimedeanField→OrderedField

ArchimedeanField→Poset : ArchimedeanField ℓ ℓ' → Poset ℓ ℓ'
ArchimedeanField→Poset = OrderedField→Poset ∘ ArchimedeanField→OrderedField

ArchimedeanField→Quoset : ArchimedeanField ℓ ℓ' → Quoset ℓ ℓ'
ArchimedeanField→Quoset = OrderedField→Quoset ∘ ArchimedeanField→OrderedField

module _ (A : ArchimedeanField ℓ ℓ') where
  private
    AOF  = ArchimedeanField→OrderedField A

  open ArchimedeanFieldStr (snd A)

  module ArchimedeanFieldReasoning where
    open OrderedFieldReasoning AOF public
    open ℚ↪Reasoning AOF (ι , isOrderedFieldHomι) public

  module ArchimedeanFieldTheory where
    open OrderedFieldTheory AOF public
    open ℚ↪Theory AOF (ι , isOrderedFieldHomι) public
