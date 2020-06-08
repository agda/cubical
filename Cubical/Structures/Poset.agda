{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Poset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv        renaming (_■ to _QED)
open import Cubical.Foundations.SIP          renaming (SNS-≡ to SNS)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

-- We will adopt the convention of denoting the level of the carrier
-- set by ℓ₀ and the level of the relation result by ℓ₁.
private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₀′ ℓ₁′ ℓ₀′′ ℓ₁′′ : Level

Order : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
Order ℓ₁ A = A → A → hProp ℓ₁

isSetOrder : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
isSetOrder ℓ₁ A = isSetΠ2 λ _ _ → isSetHProp

-- We first start by defining what it means a for a function to be
-- order-preserving. The name "monotonic" is reserved for partial orders.

isOrderPreserving : (M : TypeWithStr ℓ₀ (Order ℓ₁)) (N : TypeWithStr ℓ₀′ (Order ℓ₁′))
                  → (fst M → fst N) → Type _
isOrderPreserving (A , _⊑₀_) (B , _⊑₁_) f =
  (x y : A) → [ x ⊑₀ y ] → [ f x ⊑₁ f y ]

isPropIsOrderPreserving : (M : TypeWithStr ℓ₀  (Order ℓ₁))
                          (N : TypeWithStr ℓ₀′ (Order ℓ₁′))
                        → (f : fst M → fst N)
                        → isProp (isOrderPreserving M N f)
isPropIsOrderPreserving M (_ , _⊑₁_) f = isPropΠ3 λ x y p → snd (f x ⊑₁ f y)

-- We then define what it means for an equivalence to order-preserving which is
-- nothing but the property that both directions of the equivalence are
-- order-preserving.

isAnOrderPreservingEqv : (M : TypeWithStr ℓ₀  (Order ℓ₁))
                         (N : TypeWithStr ℓ₀′ (Order ℓ₁′))
                       → fst M ≃ fst N → Type _
isAnOrderPreservingEqv M N e@(f , _) =
  isOrderPreserving M N f × isOrderPreserving N M g
  where
    g = equivFun (invEquiv e)

Order-is-SNS : SNS {ℓ} (Order ℓ₁) isAnOrderPreservingEqv
Order-is-SNS {ℓ = ℓ} {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ =
  f , record { equiv-proof = f-equiv }
  where
    f : isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f e@(φ , ψ) = funExt₂ λ x y → ⇔toPath (φ x y) (ψ x y)

    g : _⊑₀_ ≡ _⊑₁_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X)
    g p =
      subst
        (λ _⊑_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑_) (idEquiv X))
        p
        ((λ _ _ x⊑₁y → x⊑₁y) , λ _ _ x⊑₁y → x⊑₁y)

    ret-f-g : retract f g
    ret-f-g (φ , ψ) =
      isPropΣ
        (isPropIsOrderPreserving (X , _⊑₀_) (X , _⊑₁_) (idfun X))
        (λ _ → isPropIsOrderPreserving (X , _⊑₁_) (X , _⊑₀_) (idfun X))
        (g (f (φ , ψ))) (φ , ψ)

    f-equiv : (p : _⊑₀_ ≡ _⊑₁_) → isContr (fiber f p)
    f-equiv p = ((to , from) , eq) , NTS
      where
        to : isOrderPreserving (X , _⊑₀_) (X , _⊑₁_) (idfun _)
        to x y = subst (λ _⊑_ → [ x ⊑₀ y ] → [ x ⊑ y ]) p (idfun _)

        from : isOrderPreserving (X , _⊑₁_) (X , _⊑₀_) (idfun _)
        from x y = subst (λ _⊑_ → [ x ⊑ y ] → [ x ⊑₀ y ]) p (idfun _)

        eq : f (to , from) ≡ p
        eq = isSetOrder ℓ₁ X _⊑₀_ _⊑₁_ (f (to , from)) p

        NTS : (fib : fiber f p) → ((to , from) , eq) ≡ fib
        NTS ((φ , ψ) , eq) =
          Σ≡Prop
            (λ i′ → isOfHLevelSuc 2 (isSetOrder ℓ₁ X) _⊑₀_ _⊑₁_ (f i′) p)
            (Σ≡Prop
               (λ _ → isPropIsOrderPreserving (X , _⊑₁_) (X , _⊑₀_) (idfun _))
               (isPropIsOrderPreserving (X , _⊑₀_) (X , _⊑₁_) (idfun _) to φ))

-- We now write down the axioms for a partial order and define posets on top of
-- raw ordered structures.

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

-- Definition of a monotonic map amounts to forgetting the partial order axioms.
isMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type _
isMonotonic (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) =
  isOrderPreserving (A , _⊑₀_) (B , _⊑₁_)

isPropIsMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′)
                  → (f : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                  → isProp (isMonotonic P Q f)
isPropIsMonotonic (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) f =
  isPropIsOrderPreserving (A , _⊑₀_) (B , _⊑₁_) f

-- We collect the type of monotonic maps between two posets in the following
-- type.

_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Type _
_─m→_ P Q = Σ[ f ∈ (∣ P ∣ₚ → ∣ Q ∣ₚ) ] (isMonotonic P Q f)

-- The identity monotonic map and composition of monotonic maps.

𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = idfun ∣ P ∣ₚ , (λ x y x⊑y → x⊑y)

_∘m_ : {P : Poset ℓ₀ ℓ₁} {Q : Poset ℓ₀′ ℓ₁′} {R : Poset ℓ₀′′ ℓ₁′′}
     → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

forget-mono : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′)
              ((f , f-mono) (g , g-mono) : P ─m→ Q)
            → f ≡ g
            → (f , f-mono) ≡ (g , g-mono)
forget-mono P Q (f , f-mono) (g , g-mono) =
  Σ≡Prop (λ f → isPropΠ3 λ x y x⊑y → snd (f x ⊑[ Q ] f y))

module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■

-- Univalence for posets.

isAMonotonicEqv : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′)
                → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type _
isAMonotonicEqv (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) =
  isAnOrderPreservingEqv (A , _⊑₀_) (B , _⊑₁_)

isPropIsAMonotonicEqv : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀ ℓ₁′)
                      → (eqv : ∣ P ∣ₚ ≃ ∣ Q ∣ₚ)
                      → isProp (isAMonotonicEqv P Q eqv)
isPropIsAMonotonicEqv P Q e@(f , _) =
  isPropΣ (isPropIsMonotonic P Q f) λ _ → isPropIsMonotonic Q P g
  where
    g = equivFun (invEquiv e)

-- We denote by `_≃ₚ_` the type of monotonic poset equivalences.

_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type _
_≃ₚ_ P Q = Σ[ i ∈ ∣ P ∣ₚ ≃ ∣ Q ∣ₚ ] isAMonotonicEqv P Q i

-- From this, we can already establish that posets form an SNS and prove that
-- the category of posets is univalent.

poset-is-SNS : SNS {ℓ} (PosetStr ℓ₁) isAMonotonicEqv
poset-is-SNS {ℓ₁ = ℓ₁} =
  SNS-PathP→SNS-≡
    (PosetStr ℓ₁)
    isAMonotonicEqv
    (add-axioms-SNS _ NTS (SNS-≡→SNS-PathP isAnOrderPreservingEqv Order-is-SNS))
  where
    NTS : (A : Type ℓ) (_⊑_ : Order ℓ₁ A) → isProp [ satPosetAx ℓ₁ A _⊑_ ]
    NTS A _⊑_ = snd (satPosetAx ℓ₁ A _⊑_)

poset-univ₀ : (P Q : Poset ℓ₀ ℓ₁) → (P ≃ₚ Q) ≃ (P ≡ Q)
poset-univ₀ = SIP (SNS-≡→SNS-PathP isAMonotonicEqv poset-is-SNS)

-- This result is almost what we want but it is better talk directly about poset
-- _isomorphisms_ rather than equivalences. In the case when types `A` and `B`
-- are sets, the type of isomorphisms between `A` and `B` is equivalent to the
-- type of equivalences betwee them.

-- Let us start by writing down what a poset isomorphisms is.

isPosetIso : (P Q : Poset ℓ₀ ℓ₁) → (P ─m→ Q) → Type _
isPosetIso P Q (f , _) = Σ[ (g , _) ∈ (Q ─m→ P) ] section f g × retract f g

isPosetIso-prop : (P Q : Poset ℓ₀ ℓ₁) (f : P ─m→ Q)
                → isProp (isPosetIso P Q f)
isPosetIso-prop P Q (f , f-mono) (g₀ , sec₀ , ret₀) (g₁ , sec₁ , ret₁) =
  Σ≡Prop NTS g₀=g₁
  where
    NTS : ((g , _) : Q ─m→ P) → isProp (section f g × retract f g)
    NTS (g , g-mono) = isPropΣ
                         (isPropΠ λ x → carrier-is-set Q (f (g x)) x) λ _ →
                          isPropΠ λ x → carrier-is-set P (g (f x)) x

    g₀=g₁ : g₀ ≡ g₁
    g₀=g₁ =
      forget-mono Q P g₀ g₁ (funExt λ x →
        fst g₀ x              ≡⟨ sym (cong (λ - → fst g₀ -) (sec₁ x)) ⟩
        fst g₀ (f (fst g₁ x)) ≡⟨ ret₀ (fst g₁ x) ⟩
        fst g₁ x              ∎)

-- We will denote by `P ≅ₚ Q` the type of isomorphisms between posets `P` and
-- `Q`.

_≅ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type _
P ≅ₚ Q = Σ[ f ∈ P ─m→ Q ] isPosetIso P Q f

-- ≅ₚ is equivalent to ≃ₚ.

≃ₚ≃≅ₚ : (P Q : Poset ℓ₀ ℓ₁) → (P ≅ₚ Q) ≃ (P ≃ₚ Q)
≃ₚ≃≅ₚ P Q = isoToEquiv (iso from to ret sec)
  where
    to : P ≃ₚ Q → P ≅ₚ Q
    to (e@(f , _) , (f-mono , g-mono)) =
      (f , f-mono) , (g , g-mono) , sec-f-g , ret-f-g
      where
        is = equivToIso e
        g  = equivFun (invEquiv e)

        sec-f-g : section f g
        sec-f-g = Iso.rightInv (equivToIso e)

        ret-f-g : retract f g
        ret-f-g = Iso.leftInv (equivToIso e)

    from : P ≅ₚ Q → P ≃ₚ Q
    from ((f , f-mono) , ((g , g-mono) , sec , ret)) =
      isoToEquiv is , f-mono , g-mono
      where
        is : Iso ∣ P ∣ₚ ∣ Q ∣ₚ
        is = iso f g sec ret

    sec : section to from
    sec (f , _) = Σ≡Prop (isPosetIso-prop P Q) refl

    ret : retract to from
    ret (e , _) = Σ≡Prop (isPropIsAMonotonicEqv P Q) (Σ≡Prop isPropIsEquiv refl)

-- Once we have this equivalence, the main result is then: the type of poset
-- isomorphisms between `P` and `Q` is equivalent to the type of identity proofs
-- between `P` and `Q`

poset-univ : (P Q : Poset ℓ₀ ℓ₁) → (P ≅ₚ Q) ≃ (P ≡ Q)
poset-univ P Q = P ≅ₚ Q ≃⟨ ≃ₚ≃≅ₚ P Q ⟩ P ≃ₚ Q ≃⟨ poset-univ₀ P Q ⟩ P ≡ Q QED
