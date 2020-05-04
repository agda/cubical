{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Poset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv        hiding   (_■)
open import Cubical.Foundations.SIP          renaming (SNS-≡ to SNS)
open import Cubical.Core.Primitives
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

-- We will adopt the convention of denoting the level of the carrier
-- set by ℓ₀ and the level of the relation result by ℓ₁.
private
  variable
    ℓ₀ ℓ₁ : Level

Order : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
Order ℓ₁ A = A → A → hProp ℓ₁

order-iso : (M N : Σ (Type ℓ₀) (Order ℓ₁)) →  fst M ≃ fst N → Type (ℓ-max ℓ₀ ℓ₁)
order-iso (A , _⊑₀_) (B , _⊑₁_) (f , _) = (x y : A) → [ x ⊑₀ y ⇔ f x ⊑₁ f y ]

isSetOrder : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
isSetOrder ℓ₁ A = isSetΠ2 λ _ _ → isSetHProp

Order-is-SNS : SNS {ℓ₀} (Order ℓ₁) order-iso
Order-is-SNS {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ = f , f-equiv
  where
    f : order-iso (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f i = funExt λ x → funExt λ y → ⇔toPath (fst (i x y)) (snd (i x y))

    ⇔-prop : isProp ((x y : X) → [ x ⊑₀ y ⇔ x ⊑₁ y ])
    ⇔-prop = isPropΠ2 λ x y → snd (x ⊑₀ y ⇔ x ⊑₁ y)

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , sec eq) , h eq }
      where
        g : (eq : _⊑₀_ ≡ _⊑₁_)
          → (x y : X)
          → ([ x ⊑₀ y ] → [ x ⊑₁ y ]) × ([ x ⊑₁ y ] → [ x ⊑₀ y ])
        g eq x y = subst (λ { _⊑⋆_ → [ x ⊑⋆ y ] }) eq
                 , subst (λ { _⊑⋆_ → [ x ⊑⋆ y ] }) (sym eq)

        sec : section f g
        sec p = isSetOrder _ X _⊑₀_ _⊑₁_ (f (g p)) p

        h : (p : _⊑₀_ ≡ _⊑₁_) → (fib : fiber f p) → (g p , sec p) ≡ fib
        h p (i , _) = ΣProp≡ A-prop B-prop
          where
            A-prop = λ i′ → isOfHLevelSuc 2 (isSetOrder ℓ₁ X) _⊑₀_ _⊑₁_ (f i′) p
            B-prop = ⇔-prop (g p) i

-- We now write down the axioms for a partial order.

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isReflexive {A = X} _⊑_ = ((x : X) → [ x ⊑ x ]) , isPropΠ λ x → snd (x ⊑ x)

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ-max ℓ₀ ℓ₁)
    φ      = ((x y z : X) → [ x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z ])
    φ-prop : isProp φ
    φ-prop = isPropΠ3 λ x y z → snd (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isAntisym {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} A-set _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ-max ℓ₀ ℓ₁)
    φ      = ((x y : X) → [ x ⊑ y ] → [ y ⊑ x ] → x ≡ y)
    φ-prop : isProp φ
    φ-prop = isPropΠ3 λ x y z → isPropΠ λ _ → A-set x y

-- The predicate expressing that a given order satisfies the partial order
-- axioms.
satPosetAx : (ℓ₁ : Level) (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
satPosetAx {ℓ₀ = ℓ₀} ℓ₁ A _⊑_ = φ , φ-prop
  where
    isPartial : isSet A → hProp (ℓ-max ℓ₀ ℓ₁)
    isPartial A-set = isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_

    φ         = Σ[ A-set ∈ isSet A ] [ isPartial A-set ]
    φ-prop    = isOfHLevelΣ 1 isPropIsSet (λ x → snd (isPartial x))

-- The poset structure.
PosetStr : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
PosetStr ℓ₁ = add-to-structure (Order ℓ₁) λ A _⊑_ → [ satPosetAx ℓ₁ A _⊑_ ]

PosetStr-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (PosetStr ℓ₁ A)
PosetStr-set ℓ₁ A =
  isSetΣ
    (isSetΠ2 λ _ _ → isSetHProp) λ _⊑_ →
      isProp→isSet (snd (satPosetAx ℓ₁ A _⊑_))

Poset : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
Poset ℓ₀ ℓ₁ = TypeWithStr ℓ₀ (PosetStr ℓ₁)

-- Some projections for syntactic convenience.

-- Carrier set of a poset.
∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ X , _ ∣ₚ = X

strₚ : (P : Poset ℓ₀ ℓ₁) → PosetStr ℓ₁ ∣ P ∣ₚ
strₚ (_ , s) = s

rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁
rel (_ , _⊑_ , _) = _⊑_

syntax rel P x y = x ⊑[ P ] y

⊑[_]-refl : (P : Poset ℓ₀ ℓ₁) → (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
⊑[_]-refl (_ , _ , _ , ⊑-refl , _) = ⊑-refl

⊑[_]-trans : (P : Poset ℓ₀ ℓ₁) (x y z : ∣ P ∣ₚ)
           → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
⊑[_]-trans (_ , _ , _ , _ , ⊑-trans , _) = ⊑-trans

⊑[_]-antisym : (P : Poset ℓ₀ ℓ₁) (x y : ∣ P ∣ₚ)
             → [ x ⊑[ P ] y ] → [ y ⊑[ P ] x ] → x ≡ y
⊑[_]-antisym (_ , _ , _ , _ , _ , ⊑-antisym) = ⊑-antisym

carrier-is-set : (P : Poset ℓ₀ ℓ₁) → isSet ∣ P ∣ₚ
carrier-is-set (_ , _ , is-set , _) = is-set

module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■

-- Poset univalence.
RP-iso-prop : (P Q : Σ (Type ℓ₀) (Order ℓ₁))
            → (eqv : fst P ≃ fst Q) → isProp (order-iso P Q eqv)
RP-iso-prop (A , _⊑₀_) (B , _⊑₁_) (f , _) =
  isPropΠ2 λ x y → snd (x ⊑₀ y ⇔ f x ⊑₁ f y)

poset-iso : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ-max ℓ₀ ℓ₁)
poset-iso {ℓ₁ = ℓ₁} = add-to-iso order-iso (λ A _⊑_ → [ satPosetAx ℓ₁ A _⊑_ ])

-- We collect poset isomorphisms in the following type.
_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
_≃ₚ_ P Q = Σ[ i ∈ (∣ P ∣ₚ ≃ ∣ Q ∣ₚ) ] poset-iso P Q i

poset-ax-props : (A : Type ℓ₀) (str : Order ℓ₁ A)
                   → isProp [ satPosetAx ℓ₁ A str ]
poset-ax-props {ℓ₁ = ℓ₁} A str = snd (satPosetAx ℓ₁ A str)

poset-is-SNS : SNS {ℓ₀} (PosetStr ℓ₁) poset-iso
poset-is-SNS {ℓ₁ = ℓ₁} =
    SNS-PathP→SNS-≡ _ poset-iso (add-axioms-SNS _ poset-ax-props isSNS-PathP)
  where
    isSNS-PathP : SNS-PathP (Order ℓ₁) order-iso
    isSNS-PathP = SNS-≡→SNS-PathP order-iso Order-is-SNS

poset-is-SNS-PathP : SNS-PathP {ℓ₀} (PosetStr ℓ₁) poset-iso
poset-is-SNS-PathP = SNS-≡→SNS-PathP poset-iso poset-is-SNS

poset-SIP : (A : Type ℓ₀) (B : Type ℓ₀) (eqv : A ≃ B)
            (P : PosetStr ℓ₁ A) (Q : PosetStr ℓ₁ B)
          → poset-iso (A , P) (B , Q) eqv
          → (A , P) ≡ (B , Q)
poset-SIP {ℓ₁ = ℓ₁} A B eqv P Q i = φ (eqv , i)
  where
    φ : (A , P) ≃[ poset-iso ] (B , Q) → (A , P) ≡ (B , Q)
    φ = equivFun (SIP poset-is-SNS-PathP (A , P) (B , Q))

≃ₚ→≡ : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
≃ₚ→≡ (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i
