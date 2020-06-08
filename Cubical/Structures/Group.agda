{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)


private
  variable
    ℓ ℓ' : Level

raw-group-structure : Type ℓ → Type ℓ
raw-group-structure = raw-semigroup-structure

raw-group-is-SNS : SNS {ℓ} raw-group-structure _
raw-group-is-SNS = raw-semigroup-is-SNS

-- The neutral element and the inverse function will be derived from the
-- axioms, instead of being defined in the raw-group-structure in order
-- to have that isomorphisms between groups are equivalences that preserves
-- multiplication (so we don't have to show that they also preserve inversion
-- and neutral element, although they will preserve them).

group-axioms : (G : Type ℓ) → raw-group-structure G → Type ℓ
group-axioms G _·_ = i × ii

  where
  i = semigroup-axioms G _·_

  ii = Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x)) ×
                  ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e))

group-structure : Type ℓ → Type ℓ
group-structure = add-to-structure raw-group-structure group-axioms

Group : Type (ℓ-suc ℓ)
Group {ℓ} = TypeWithStr ℓ group-structure

-- Extracting components of a group
⟨_⟩ : Group {ℓ} → Type ℓ
⟨ G , _ ⟩ = G

group-operation : (G : Group {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-operation (_ , f , _) = f

module group-operation-syntax where

  group-operation-syntax : (G : Group {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  group-operation-syntax = group-operation
  infixr 20 group-operation-syntax
  syntax group-operation-syntax G x y = x ·⟨ G ⟩ y

open group-operation-syntax

group-is-set : (G : Group {ℓ}) → isSet ⟨ G ⟩
group-is-set (_ , _ , (P , _) , _) = P

group-assoc : (G : Group {ℓ})
            → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
group-assoc (_ , _ , (_ , P) , _) = P

-- Defining identity

group-id : (G : Group {ℓ}) → ⟨ G ⟩
group-id (_ , _ , _ , P) = fst P

group-rid : (G : Group {ℓ})
          → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (group-id G) ≡ x
group-rid (_ , _ , _ , P) x = fst ((fst (snd P)) x)

group-lid : (G : Group {ℓ})
          → (x : ⟨ G ⟩) → (group-id G) ·⟨ G ⟩ x ≡ x
group-lid (_ , _ , _ , P) x = snd ((fst (snd P)) x)

-- Defining the inverse function
group-inv : (G : Group {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩
group-inv (_ , _ , _ , P) x = fst ((snd (snd P)) x)

group-rinv : (G : Group {ℓ})
               → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (group-inv G x) ≡ group-id G
group-rinv (_ , _ , _ , P) x = fst (snd ((snd (snd P)) x))

group-linv : (G : Group {ℓ})
               → (x : ⟨ G ⟩) → (group-inv G x) ·⟨ G ⟩ x ≡ group-id G
group-linv (_ , _ , _ , P) x = snd (snd ((snd (snd P)) x))

-- Iso for groups are those for monoids
group-iso : StrIso group-structure ℓ
group-iso = add-to-iso (nAryFunIso 2) group-axioms

-- Group axioms isProp

group-axioms-isProp : (X : Type ℓ)
                    → (s : raw-group-structure X)
                    → isProp (group-axioms X s)
group-axioms-isProp X s t = η t
  where
  𝒢 : Group
  𝒢 = X , s , t

  is-identity : X → Type _
  is-identity e = (x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)

  α : (e : X) → isProp (is-identity e)
  α e = isPropΠ (λ _ → isPropΣ (group-is-set 𝒢 _ _) (λ _ → group-is-set 𝒢 _ _))

  β : (e : X) → is-identity e → isProp ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e))
  β e is-identity-e =
   isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
   Σ≡Prop
     (λ _ → isPropΣ (group-is-set 𝒢 _ _) (λ _ → group-is-set 𝒢 _ _))
     (inv-lemma ℳ x x' x'' P Q) }
   where
    ℳ : Monoid
    ℳ = ⟨ 𝒢 ⟩ , (e , group-operation 𝒢) ,
        group-is-set 𝒢 ,
        group-assoc 𝒢 ,
        (λ x → fst (is-identity-e x)) ,
        (λ x → snd (is-identity-e x))


  γ : isProp (Σ[ e ∈ X ] ((x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)) ×
                         ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e)))
  γ (e , P , _) (e' , Q , _) = Σ≡Prop (λ e → isPropΣ (α e) λ is-identity-e → β e is-identity-e)
                                      (e          ≡⟨ sym (fst (Q e)) ⟩
                                      e ·⟨ 𝒢 ⟩ e' ≡⟨ snd (P e') ⟩
                                      e' ∎)

  η : isProp (group-axioms X s)
  η = isPropΣ (semigroup-axiom-isProp X s) λ _ → γ

-- Group paths equivalent to equality
group-is-SNS : SNS {ℓ} group-structure group-iso
group-is-SNS = add-axioms-SNS _ group-axioms-isProp (nAryFunSNS 2)

GroupPath : (M N : Group {ℓ}) → (M ≃[ group-iso ] N) ≃ (M ≡ N)
GroupPath = SIP group-is-SNS

-- Group ·syntax

module group-·syntax (G : Group {ℓ}) where

  infixr 18 _·_

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _·_ = group-operation G

  ₁ : ⟨ G ⟩
  ₁ = group-id G

  infix 19 _⁻¹

  _⁻¹ : ⟨ G ⟩ → ⟨ G ⟩
  _⁻¹ = group-inv G
