module Cubical.Categories.Instances.Lattices where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Lattice

open import Cubical.Categories.Category

open Category
open LatticeHoms

LatticesCategory : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
ob LatticesCategory       = Lattice _
Hom[_,_] LatticesCategory = LatticeHom
id LatticesCategory {L}   = idLatticeHom L
_⋆_ LatticesCategory      = compLatticeHom
⋆IdL LatticesCategory     = compIdLatticeHom
⋆IdR LatticesCategory     = idCompLatticeHom
⋆Assoc LatticesCategory   = compAssocLatticeHom
isSetHom LatticesCategory = isSetLatticeHom _ _
