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
module Cubical.Algebra.Group.Morphisms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

record IsGroupHom {A : Type ℓ} {B : Type ℓ'}
  (M : GroupStr A) (f : A → B) (N : GroupStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module M = GroupStr M
    module N = GroupStr N

  field
    pres· : (x y : A) → f (x M.· y) ≡ f x N.· f y
    pres1 : f M.1g ≡ N.1g
    presinv : (x : A) → f (M.inv x) ≡ N.inv (f x)

unquoteDecl IsGroupHomIsoΣ = declareRecordIsoΣ IsGroupHomIsoΣ (quote IsGroupHom)

GroupHom : (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
GroupHom G H = Σ[ f ∈ (G .fst → H .fst) ] IsGroupHom (G .snd) f (H .snd)

GroupIso : (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
GroupIso G H = Σ[ e ∈ Iso (G .fst) (H .fst) ] IsGroupHom (G .snd) (e .Iso.fun) (H .snd)

IsGroupEquiv : {A : Type ℓ} {B : Type ℓ'}
  (M : GroupStr A) (e : A ≃ B) (N : GroupStr B) → Type (ℓ-max ℓ ℓ')
IsGroupEquiv M e N = IsGroupHom M (e .fst) N

GroupEquiv : (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
GroupEquiv G H = Σ[ e ∈ (G .fst ≃ H .fst) ] IsGroupEquiv (G .snd) e (H .snd)

groupEquivFun : {G : Group ℓ} {H : Group ℓ'} → GroupEquiv G H → G .fst → H .fst
groupEquivFun e = e .fst .fst

-- Image, kernel, surjective, injective, and bijections

open IsGroupHom
open GroupStr

private
  variable
    G H : Group ℓ

isInIm : GroupHom G H → ⟨ H ⟩ → Type _
isInIm {G = G} ϕ h = ∃[ g ∈ ⟨ G ⟩ ] ϕ .fst g ≡ h

isInKer : GroupHom G H → ⟨ G ⟩ → Type _
isInKer {H = H} ϕ g = ϕ .fst g ≡ 1g (snd H)

Ker : GroupHom G H → Type _
Ker {G = G} ϕ = Σ[ x ∈ ⟨ G ⟩ ] isInKer ϕ x

Im : GroupHom G H → Type _
Im {H = H} ϕ = Σ[ x ∈ ⟨ H ⟩ ] isInIm ϕ x

isSurjective : GroupHom G H → Type _
isSurjective {H = H} ϕ = (x : ⟨ H ⟩) → isInIm ϕ x

isInjective : GroupHom G H → Type _
isInjective {G = G} ϕ = (x : ⟨ G ⟩) → isInKer ϕ x → x ≡ 1g (snd G)

isMono : GroupHom G H → Type _
isMono {G = G} f = {x y : ⟨ G ⟩} → f .fst x ≡ f .fst y → x ≡ y

-- Group bijections
record BijectionIso (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor bijIso

  field
    fun : GroupHom G H
    inj : isInjective fun
    surj : isSurjective fun
