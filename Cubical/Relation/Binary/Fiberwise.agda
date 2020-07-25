{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary.Base
open BinaryRelation


private
  variable
    ℓA ℓA' ℓB ℓ≅B ℓ≅B' ℓB' : Level

-- given a type A, this is the type of relational families on A
RelFamily : (A : Type ℓA) (ℓB ℓ≅B : Level) → Type (ℓ-max (ℓ-max ℓA (ℓ-suc ℓB)) (ℓ-suc ℓ≅B))
RelFamily A ℓB ℓ≅B = Σ[ B ∈ (A → Type ℓB) ] ({a : A} → Rel (B a) (B a) ℓ≅B)

-- property for a relational family to be fiberwise reflexive
isFiberwiseReflexive : {A : Type ℓA} {ℓB ℓ≅B : Level}
                       (B : RelFamily A ℓB ℓ≅B)
                       → Type (ℓ-max (ℓ-max ℓA ℓB) ℓ≅B)
isFiberwiseReflexive {A = A} (B , _≅_) = {a : A} → isRefl (_≅_ {a = a})

-- property for a relational fiberwise reflexive family to be fiberwise univalent:
isFiberwiseUnivalent : {A : Type ℓA} {ℓB ℓ≅B : Level}
                       (B : RelFamily A ℓB ℓ≅B)
                       (ρ : isFiberwiseReflexive B)
                       → Type (ℓ-max (ℓ-max ℓA ℓB) ℓ≅B)
isFiberwiseUnivalent {A = A} (B , _≅_) ρ = {a : A} → isUnivalent (_≅_ {a = a}) (ρ {a = a})

-- pulling back a relational family along a map
♭RelFamily : {A : Type ℓA} {A' : Type ℓA'}
             {ℓB ℓ≅B : Level} (B : RelFamily A' ℓB ℓ≅B)
             (f : A → A')
             → RelFamily A ℓB ℓ≅B
♭RelFamily (B , _) f .fst a = B (f a)
♭RelFamily (_ , _≅_) f .snd = _≅_

module _ {A : Type ℓA} {A' : Type ℓA'} (f : A ≃ A')
         (B : RelFamily A ℓB ℓ≅B) (ρ : isFiberwiseReflexive B) (uni : isFiberwiseUnivalent B ρ)
         (B' : RelFamily A' ℓB' ℓ≅B') (ρ' : isFiberwiseReflexive B') (uni' : isFiberwiseUnivalent B' ρ') where

       ♭B' = ♭RelFamily B' (fst f)

       RelFiberIsoOver→FiberIso : (a : A) (e≅♭ : RelIso (B .snd {a = a}) (♭B' .snd {a = a}))
                                  → Iso (B .fst a) (B' .fst (f .fst a))
       RelFiberIsoOver→FiberIso a e≅♭ = iso fun inv (λ b' → invEquiv (≡→R (snd B') ρ' , uni' (fun (inv b')) b') .fst (rightInv b'))
                                                    λ b → invEquiv (≡→R (snd B) ρ , uni (inv (fun b)) b) .fst (leftInv b)
         where
           open RelIso e≅♭
