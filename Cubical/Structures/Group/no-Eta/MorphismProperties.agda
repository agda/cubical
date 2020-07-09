{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group.no-Eta.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open import Cubical.Structures.Group.no-Eta.Base
open import Cubical.Structures.Group.no-Eta.Properties
open import Cubical.Structures.Group.no-Eta.Morphism

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level

infixr 31 _□_

isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → Group.is-set H _ _


-- Morphism composition

open GroupHom
open GroupEquiv
isGroupHomComp : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (GroupHom.fun g ∘ GroupHom.fun f)
isGroupHomComp F G x y =
  cong (fun G) (isHom F _ _) ∙ isHom G _ _

compGroupHom : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupHom F G → GroupHom G H → GroupHom F H
fun (compGroupHom {F = F} {G = G} {H = H} f g) = fun g ∘ fun f
isHom (compGroupHom {F = F} {G = G} {H = H} f g) = isGroupHomComp f g

compGroupEquiv : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
GroupEquiv.eq (compGroupEquiv {F = F} {G = G} {H = H} f g) = compEquiv (eq f) (eq g)
GroupEquiv.isHom (compGroupEquiv {F = F} {G = G} {H = H} f g) = isHom (compGroupHom (hom f) (hom g))

_□_ : _
_□_ = compGroupEquiv


idGroupEquiv : (G : Group {ℓ}) → GroupEquiv G G
eq (idGroupEquiv G) = idEquiv ⟨ G ⟩
isHom (idGroupEquiv G) = λ _ _ → refl

-- Isomorphism inversion
isGroupHomInv : {G : Group {ℓ}} {H : Group {ℓ'}} (f : GroupEquiv G H) → isGroupHom H G (invEq (GroupEquiv.eq f))
isGroupHomInv {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ retEq (eq f) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (retEq (eq f) h) (retEq (eq f) h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (hom f) _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fst (eq f)
  _⋆¹_ = Group._+_ G
  _⋆²_ = Group._+_ H
  g = invEq (eq f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (eq f)) x y)

invGroupEquiv : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupEquiv G H → GroupEquiv H G
eq (invGroupEquiv f) = invEquiv (eq f)
isHom (invGroupEquiv f) = isGroupHomInv f
