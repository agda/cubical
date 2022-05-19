{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)

private variable
  ℓ ℓ' : Level
  A : Type ℓ

module _ {X : Type ℓ} (A : X → AbGroup ℓ) where

  infixl 7 _⊕_
  infix 20 ⊖_

  open AbGroupStr ⦃...⦄ using (_+_)
  private
    instance
      givenAbGroupStr : {x : X} → AbGroupStr _
      givenAbGroupStr {x} = snd (A x)

  data Coproduct : Type ℓ where
    incl       : {x : X} → ⟨ A x ⟩ → Coproduct
    ε         : Coproduct
    _⊕_       : Coproduct → Coproduct → Coproduct
    ⊖_       : Coproduct → Coproduct
    inclPres+ : {x : X} → (a b : ⟨ A x ⟩) → incl (a + b) ≡ (incl a) ⊕ (incl b)
    assoc     : ∀ x y z → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    comm      : ∀ x y   → x ⊕ y       ≡ y ⊕ x
    identityᵣ : ∀ x     → x ⊕ ε       ≡ x
    invᵣ      : ∀ x     → x ⊕ (⊖ x)   ≡ ε
    trunc     : isSet Coproduct

  module Elim {B : Coproduct → Type ℓ'}
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B (incl a))
    (ε*         : B ε)
    (_⊕*_       : ∀ {x y}   → B x → B y → B (x ⊕ y))
    (⊖*_       : ∀ {x}     → B x → B (⊖ x))
    (inclPres+* : {x : X} → (a b : ⟨ A x ⟩)
      → PathP (λ i → B (inclPres+ a b i)) (incl* _ (a + b)) (incl* _ a ⊕* incl* _ b))
    (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
      → PathP (λ i → B (assoc x y z i)) (xs ⊕* (ys ⊕* zs)) ((xs ⊕* ys) ⊕* zs))
    (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
      → PathP (λ i → B (comm x y i)) (xs ⊕* ys) (ys ⊕* xs))
    (identityᵣ* : ∀ {x}     → (xs : B x)
      → PathP (λ i → B (identityᵣ x i)) (xs ⊕* ε*) xs)
    (invᵣ* : ∀ {x} → (xs : B x)
      → PathP (λ i → B (invᵣ x i)) (xs ⊕* (⊖* xs)) ε*)
    (trunc*     : ∀ xs → isSet (B xs)) where

    f : (x : Coproduct) → B x
    f (incl a) = incl* _ a
    f ε = ε*
    f (x ⊕ y) = f x ⊕* f y
    f (⊖ x) = ⊖* (f x)
    f (inclPres+ a b i) = {!!}
    f (assoc x y z i) = assoc* (f x) (f y) (f z) i
    f (comm x y i) = comm* (f x) (f y) i
    f (identityᵣ x i) = identityᵣ* (f x) i
    f (invᵣ x i) = invᵣ* (f x) i
    f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f x) (f y)
      (cong f p) (cong f q) (trunc x y p q) i j

  module ElimProp {B : Coproduct → Type ℓ'}
    (BProp : {xs : Coproduct} → isProp (B xs))
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B (incl a))
    (ε*         : B ε)
    (_⊕*_       : ∀ {x y}   → B x → B y → B (x ⊕ y))
    (_⊖*       : ∀ {x}     → B x → B (⊖ x)) where

    f : (xs : Coproduct) → B xs
    f = Elim.f incl* ε* _⊕*_ _⊖*
      (λ {x} a b → toPathP (BProp (transport (λ i → B (inclPres+ a b i)) (incl* _ (a + b))) (incl* _ a ⊕* incl* _ b)))
      (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ⊕* (ys ⊕* zs))) ((xs ⊕* ys) ⊕* zs)))
      (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ⊕* ys)) (ys ⊕* xs)))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ⊕* ε*)) xs))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (invᵣ x i)) (xs ⊕* (xs ⊖*))) ε*))
      (λ _ → (isProp→isSet BProp))

  module Rec {B : Type ℓ'} (BType : isSet B)
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B)
    (ε*         : B)
    (_⊕*_       : B → B → B)
    (⊖*_       : B → B)
    (inclPres+* : {x : X} → (a b : ⟨ A x ⟩) → incl* _ (a + b) ≡ incl* _ a ⊕* incl* _ b)
    (assoc*     : (x y z : B) → x ⊕* (y ⊕* z) ≡ (x ⊕* y) ⊕* z)
    (comm*      : (x y : B)   → x ⊕* y        ≡ y ⊕* x)
    (identityᵣ* : (x : B)     → x ⊕* ε*       ≡ x)
    (invᵣ*      : (x : B)     → x ⊕* (⊖* x)  ≡ ε*)
    where

    f : Coproduct → B
    f = Elim.f incl* ε* _⊕*_ ⊖*_ inclPres+* assoc* comm* identityᵣ* invᵣ* (const BType)

  AsAbGroup : AbGroup ℓ
  AsAbGroup = makeAbGroup {G = Coproduct} ε _⊕_ ⊖_ trunc assoc identityᵣ invᵣ comm

  inclHom : (x : X) → AbGroupHom (A x) AsAbGroup
  inclHom x = (incl {x = x}) , (makeIsGroupHom inclPres+)

  module UniversalProperty (B : AbGroup ℓ') (incl* : (x : X) → AbGroupHom (A x) B)
         where
