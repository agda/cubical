{-

Defines different notions of morphisms and properties of morphisms of
groups:

- GroupHom (homomorphisms)
- GroupEquiv (equivs which are homomorphisms)
- GroupIso (isos which are homomorphisms)
- Image
- Kernel
- Surjective
- Injective
- Mono
- BijectionIso (surjective + injective)

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Morphisms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.
isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.· y) ≡ (f x H.· f y) where
  module G = GroupStr (snd G)
  module H = GroupStr (snd H)

record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor grouphom

  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : isGroupHom G H fun

record GroupEquiv (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupequiv

  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun eq)

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom

record GroupIso (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupiso

  field
    isom : Iso ⟨ G ⟩ ⟨ H ⟩
    isHom : isGroupHom G H (Iso.fun isom)

  hom : GroupHom G H
  hom = grouphom (Iso.fun isom) isHom


-- Image, kernel, surjective, injective, and bijections

open GroupHom
open GroupStr

private
  variable
    G H : Group {ℓ}

isInIm : GroupHom G H → ⟨ H ⟩ → Type _
isInIm {G = G} ϕ h = ∃[ g ∈ ⟨ G ⟩ ] ϕ .fun g ≡ h

isInKer : GroupHom G H → ⟨ G ⟩ → Type _
isInKer {H = H} ϕ g = ϕ .fun g ≡ 1g (snd H)

Ker : GroupHom G H → Type _
Ker {G = G} ϕ = Σ[ x ∈ ⟨ G ⟩ ] isInKer ϕ x

Im : GroupHom G H → Type _
Im {H = H} ϕ = Σ[ x ∈ ⟨ H ⟩ ] isInIm ϕ x

isSurjective : GroupHom G H → Type _
isSurjective {H = H} ϕ = (x : ⟨ H ⟩) → isInIm ϕ x

isInjective : GroupHom G H → Type _
isInjective {G = G} ϕ = (x : ⟨ G ⟩) → isInKer ϕ x → x ≡ 1g (snd G)

isMono : GroupHom G H → Type _
isMono {G = G} f = {x y : ⟨ G ⟩} → f .fun x ≡ f .fun y → x ≡ y

-- Group bijections
record BijectionIso (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where

  constructor bijIso

  field
    fun : GroupHom G H
    inj : isInjective fun
    surj : isSurjective fun
