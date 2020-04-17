{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid using (Monoids; inv-lemma)


private
  variable
    ℓ ℓ' : Level

raw-group-structure : Type ℓ → Type ℓ
raw-group-structure = raw-semigroup-structure

raw-group-is-SNS : SNS {ℓ} raw-group-structure _
raw-group-is-SNS = raw-semigroup-is-SNS

group-axioms : (G : Type ℓ) → raw-group-structure G → Type ℓ
group-axioms G _·_ = i × ii

  where
  i = semigroup-axioms G _·_

  ii = Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x)) ×
                  ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e))

group-structure : Type ℓ → Type ℓ
group-structure = add-to-structure raw-group-structure group-axioms

Groups : Type (ℓ-suc ℓ)
Groups {ℓ} = TypeWithStr ℓ group-structure

-- Extracting components of a group
⟨_⟩ : Groups {ℓ} → Type ℓ
⟨ G , _ ⟩ = G

group-operation : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-operation (_ , f , _) = f

module group-operation-syntax where

  group-operation-syntax : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  group-operation-syntax = group-operation
  infixl 20 group-operation-syntax
  syntax group-operation-syntax G x y = x ·⟨ G ⟩ y

open group-operation-syntax

group-is-set : (G : Groups {ℓ}) → isSet ⟨ G ⟩
group-is-set (_ , _ , (P , _) , _) = P

group-assoc : (G : Groups {ℓ})
            → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
group-assoc (_ , _ , (_ , P) , _) = P

-- Defining identity

id : (G : Groups {ℓ}) → ⟨ G ⟩
id (_ , _ , _ , P) = fst P

group-rid : (G : Groups {ℓ})
          → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (id G) ≡ x
group-rid (_ , _ , _ , P) x = fst ((fst (snd P)) x)

group-lid : (G : Groups {ℓ})
          → (x : ⟨ G ⟩) → (id G) ·⟨ G ⟩ x ≡ x
group-lid (_ , _ , _ , P) x = snd ((fst (snd P)) x)

-- Defining the inverse function
inv : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩
inv (_ , _ , _ , P) x = fst ((snd (snd P)) x)

group-rinv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (inv G x) ≡ id G
group-rinv (_ , _ , _ , P) x = fst (snd ((snd (snd P)) x))

group-linv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → (inv G x) ·⟨ G ⟩ x ≡ id G
group-linv (_ , _ , _ , P) x = snd (snd ((snd (snd P)) x))

-- Additive notation for groups
module additive-notation (G : Groups {ℓ}) where

  ₀ : ⟨ G ⟩
  ₀ = id G

  _+_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _+_ = group-operation G

  -_ : ⟨ G ⟩ → ⟨ G ⟩
  -_ = inv G

--Multiplicative notation for groups
module multiplicative-notation (G : Groups {ℓ}) where

  ₁ : ⟨ G ⟩
  ₁ = id G

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _·_ = group-operation G

  _⁻¹ : ⟨ G ⟩ → ⟨ G ⟩
  _⁻¹ = inv G

  ·-is-assoc = group-assoc G

  ·₁  = group-rid G

  ₁·  = group-lid G

  ·⁻¹ = group-rinv G

  ⁻¹· = group-linv G

-- Iso for groups are those for monoids
group-iso : StrIso group-structure ℓ
group-iso = add-to-iso (nAryFunIso 2) group-axioms

-- Group axioms isProp

group-axioms-isProp : (X : Type ℓ)
                    → (s : raw-group-structure X)
                    → isProp (group-axioms X s)
group-axioms-isProp X s t = η t
  where
  𝒢 : Groups
  𝒢 = X , s , t

  is-identity : X → Type _
  is-identity e = (x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)

  α : (e : X) → isProp (is-identity e)
  α e = isPropΠ (λ _ → isPropΣ (group-is-set 𝒢 _ _) (λ _ → group-is-set 𝒢 _ _))

  β : (e : X) → is-identity e → isProp ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e))
  β e is-identity-e =
   isPropΠ λ { x (x' , _ , P) (x'' , Q , _) → ΣProp≡ (λ _ → isPropΣ (group-is-set 𝒢 _ _) λ _ → group-is-set 𝒢 _ _)
                                                      (inv-lemma ℳ x x' x'' P Q) }
   where
    ℳ : Monoids
    ℳ = ⟨ 𝒢 ⟩ , (e , group-operation 𝒢) ,
        group-is-set 𝒢 ,
        group-assoc 𝒢 ,
        (λ x → fst (is-identity-e x)) ,
        (λ x → snd (is-identity-e x))


  γ : isProp (Σ[ e ∈ X ] ((x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)) ×
                         ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e)))
  γ (e , P , _) (e' , Q , _) = ΣProp≡ (λ e → isPropΣ (α e) λ is-identity-e → β e is-identity-e)
                                      (e          ≡⟨ sym (fst (Q e)) ⟩
                                      e ·⟨ 𝒢 ⟩ e' ≡⟨ snd (P e') ⟩
                                      e' ∎)

  η : isProp (group-axioms X s)
  η = isPropΣ (semigroup-axiom-isProp X s) λ _ → γ

-- Group paths equivalent to equality
group-is-SNS : SNS {ℓ} group-structure group-iso
group-is-SNS = add-axioms-SNS _ group-axioms-isProp (nAryFunSNS 2)

GroupPath : (M N : Groups {ℓ}) → (M ≃[ group-iso ] N) ≃ (M ≡ N)
GroupPath = SIP group-is-SNS
