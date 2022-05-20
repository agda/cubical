{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)

private variable
  ℓ ℓ' : Level
  A : Type ℓ

module _ {X : Type ℓ} (A : X → AbGroup ℓ) where

  infixl 7 _⊕_
  infix 20 ⊖_

  open AbGroupStr ⦃...⦄ using (_+_; -_; 0g)
  private
    instance
      givenAbGroupStr : {x : X} → AbGroupStr _
      givenAbGroupStr {x} = snd (A x)

  data Coproduct : Type ℓ where
    incl       : {x : X} → ⟨ A x ⟩ → Coproduct
    ε         : Coproduct
    _⊕_       : Coproduct → Coproduct → Coproduct
    ⊖_       : Coproduct → Coproduct
    inclPres+ : {x : X} → (a a' : ⟨ A x ⟩) → incl (a + a') ≡ (incl a) ⊕ (incl a')
    assoc     : ∀ a a' a'' → a ⊕ (a' ⊕ a'') ≡ (a ⊕ a') ⊕ a''
    comm      : ∀ a a'   → a ⊕ a'       ≡ a' ⊕ a
    identityᵣ : ∀ a     → a ⊕ ε       ≡ a
    invᵣ      : ∀ a     → a ⊕ (⊖ a)   ≡ ε
    trunc     : isSet Coproduct

  module _ {B : Coproduct → Type ℓ'}
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

    elim : (x : Coproduct) → B x
    elim (incl a) = incl* _ a
    elim ε = ε*
    elim (x ⊕ y) = elim x ⊕* elim y
    elim (⊖ x) = ⊖* (elim x)
    elim (inclPres+ a a' i) = inclPres+* a a' i
    elim (assoc x y z i) = assoc* (elim x) (elim y) (elim z) i
    elim (comm x y i) = comm* (elim x) (elim y) i
    elim (identityᵣ x i) = identityᵣ* (elim x) i
    elim (invᵣ x i) = invᵣ* (elim x) i
    elim (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (elim x) (elim y)
      (cong elim p) (cong elim q) (trunc x y p q) i j

  module _ {B : Coproduct → Type ℓ'}
    (BProp : {xs : Coproduct} → isProp (B xs))
    (incl*       : (x : X) (a : ⟨ A x ⟩) → B (incl a))
    (ε*         : B ε)
    (_⊕*_       : ∀ {x y}   → B x → B y → B (x ⊕ y))
    (_⊖*       : ∀ {x}     → B x → B (⊖ x)) where

    elimProp : (xs : Coproduct) → B xs
    elimProp = elim incl* ε* _⊕*_ _⊖*
      (λ {x} a b → toPathP (BProp (transport (λ i → B (inclPres+ a b i)) (incl* _ (a + b))) (incl* _ a ⊕* incl* _ b)))
      (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ⊕* (ys ⊕* zs))) ((xs ⊕* ys) ⊕* zs)))
      (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ⊕* ys)) (ys ⊕* xs)))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ⊕* ε*)) xs))
      (λ {x} xs → toPathP (BProp (transport (λ i → B (invᵣ x i)) (xs ⊕* (xs ⊖*))) ε*))
      (λ _ → (isProp→isSet BProp))

  module _ {B : Type ℓ'} (BType : isSet B)
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

    rec : Coproduct → B
    rec = elim incl* ε* _⊕*_ ⊖*_ inclPres+* assoc* comm* identityᵣ* invᵣ* (const BType)

  AsAbGroup : AbGroup ℓ
  AsAbGroup = makeAbGroup {G = Coproduct} ε _⊕_ ⊖_ trunc assoc identityᵣ invᵣ comm

  inclHom : (x : X) → AbGroupHom (A x) AsAbGroup
  inclHom x = (incl {x = x}) , (makeIsGroupHom inclPres+)

  module UniversalProperty (B : AbGroup ℓ') (incl* : (x : X) → AbGroupHom (A x) B)
         where

    private
      instance
        _ = snd B

    inducedMap : Coproduct → ⟨ B ⟩
    inducedMap x =
      rec (isSetAbGroup B) (λ x a → fst (incl* x) a) 0g _+_ -_ {!!} {!!} {!!} {!!}
        {!!} {!!}
