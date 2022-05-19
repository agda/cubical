{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup

private variable
  ℓ ℓ' : Level
  A : Type ℓ

module _ {X : Type ℓ} (A : X → AbGroup ℓ') where

  infixl 7 _·_
  infix 20 _⁻¹

  data Coproduct : Type (ℓ-max ℓ ℓ') where
    incl       : (x : X) → ⟨ A x ⟩ → Coproduct
    ε         : Coproduct
    _·_       : Coproduct → Coproduct → Coproduct
    _⁻¹       : Coproduct → Coproduct
    assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
    comm      : ∀ x y   → x · y       ≡ y · x
    identityᵣ : ∀ x     → x · ε       ≡ x
    invᵣ      : ∀ x     → x · x ⁻¹    ≡ ε
    trunc     : isSet Coproduct

  module Elim {B : Coproduct → Type ℓ'}
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B (incl x a))
    (ε*         : B ε)
    (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
    (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹))
    (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
      → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
    (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
      → PathP (λ i → B (comm x y i)) (xs ·* ys) (ys ·* xs))
    (identityᵣ* : ∀ {x}     → (xs : B x)
      → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
    (invᵣ* : ∀ {x} → (xs : B x)
      → PathP (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*)) ε*)
    (trunc*     : ∀ xs → isSet (B xs)) where

    f : (xs : Coproduct) → B xs
    f (incl x a) = incl* x a
    f ε = ε*
    f (xs · ys) = f xs ·* f ys
    f (xs ⁻¹) = f xs ⁻¹*
    f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
    f (comm xs ys i) = comm* (f xs) (f ys) i
    f (identityᵣ xs i) = identityᵣ* (f xs) i
    f (invᵣ xs i) = invᵣ* (f xs) i
    f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
      (cong f p) (cong f q) (trunc xs ys p q) i j

  module ElimProp {B : Coproduct → Type ℓ'}
    (BProp : {xs : Coproduct} → isProp (B xs))
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B (incl x a))
    (ε*         : B ε)
    (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
    (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹)) where

    f : (xs : Coproduct) → B xs
    f = Elim.f incl* ε* _·*_ _⁻¹*
      (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
      (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ·* ys)) (ys ·* xs)))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*))) ε*))
      (λ _ → (isProp→isSet BProp))

  module Rec {B : Type ℓ'} (BType : isSet B)
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B)
    (ε*         : B)
    (_·*_       : B → B → B)
    (_⁻¹*       : B → B)
    (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
    (comm*      : (x y : B)   → x ·* y        ≡ y ·* x)
    (identityᵣ* : (x : B)     → x ·* ε*       ≡ x)
    (invᵣ*      : (x : B)     → x ·* (x ⁻¹*)  ≡ ε*)
    where

    f : Coproduct → B
    f = Elim.f incl* ε* _·*_ _⁻¹* assoc* comm* identityᵣ* invᵣ* (const BType)

  AsAbGroup : AbGroup ℓ'
  AsAbGroup = ?

  inclHom : (x : X) → AbGroupHom (A x) AsAbGroup
  inclHom x = ?

  module UniversalProperty (B : AbGroup ℓ') (incl* : (x : X) → AbGroupHom (A x) B)
         where
