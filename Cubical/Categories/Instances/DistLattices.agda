module Cubical.Categories.Instances.DistLattices where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category

open Category


DistLatticesCategory : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
ob DistLatticesCategory                     = DistLattice _
Hom[_,_] DistLatticesCategory               = DistLatticeHom
id DistLatticesCategory {L}                 = idDistLatticeHom L
_⋆_ DistLatticesCategory {L} {M} {N}        = compDistLatticeHom L M N
⋆IdL DistLatticesCategory {L} {M}           = compIdDistLatticeHom {L = L} {M}
⋆IdR DistLatticesCategory {L} {M}           = idCompDistLatticeHom {L = L} {M}
⋆Assoc DistLatticesCategory {L} {M} {N} {O} = compAssocDistLatticeHom {L = L} {M} {N} {O}
isSetHom DistLatticesCategory = isSetLatticeHom _ _
