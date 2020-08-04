{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary.Base
open BinaryRelation


private
  variable
    ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓ≅B ℓ≅B' ℓB' : Level

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

-- the type of relational isomorphisms over f
♭RelFiberIsoOver : {A : Type ℓA} {A' : Type ℓA'}
                  (f : A → A')
                  (B : RelFamily A ℓB ℓ≅B)
                  (B' : RelFamily A' ℓB' ℓ≅B')
                  → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
♭RelFiberIsoOver {A = A} f B B' = (a : A) → RelIso (B .snd {a = a}) (♭B' .snd {a = a})
  where
    ♭B' = ♭RelFamily B' f

RelFiberIsoOver : {A : Type ℓA} {A' : Type ℓA'}
                  (f : A → A')
                  (B : RelFamily A ℓB ℓ≅B)
                  (B' : RelFamily A' ℓB' ℓ≅B')
                  → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
RelFiberIsoOver {A = A} f B B' = (a : A) → RelIso (B .snd {a = a}) (B' .snd {a = f a})

{-
module _ {A : Type ℓA} {_≅A_ : Rel A A ℓ≅A}
         {A' : Type ℓA'} {_≅A'_ : Rel A' A' ℓ≅A'}
         (ℱ : RelIso _≅A_ _≅A'_)
         (B : RelFamily A ℓB ℓ≅B)
         (B' : RelFamily A' ℓB' ℓ≅B') where

         f = RelIso.fun ℱ
         ♭B' = ♭RelFamily B' f
         ΣB = Σ[ a ∈ A ] (B .fst a)
         ΣB' = Σ[ a ∈ A' ] (B' .fst a)
         _≅ΣB_ : Rel ΣB ΣB {!!}
         _≅ΣB_ (a , b) (a' , b') = a ≅A a' × {!B .snd !}
         _≅ΣB'_ : Rel ΣB' ΣB' {!!}
         _≅ΣB'_ (a , b) (a' , b') = {!!}

         RelFiberIsoOver→TotalFiberIso : (ρ : isFiberwiseReflexive B) (uni : isFiberwiseUnivalent B ρ)
                                         (ρ' : isFiberwiseReflexive B') (uni' : isFiberwiseUnivalent B' ρ')
                                         (𝒢 : ♭RelFiberIsoOver f B B')
                                         → RelIso _≅ΣB_ _≅ΣB'_
         RelFiberIsoOver→TotalFiberIso 𝒢 = {!!}
-}

{-
module _ {A : Type ℓA} {A' : Type ℓA'} (f : A ≃ A')
         (B : RelFamily A ℓB ℓ≅B) (ρ : isFiberwiseReflexive B) (uni : isFiberwiseUnivalent B ρ)
         (B' : RelFamily A' ℓB' ℓ≅B') (ρ' : isFiberwiseReflexive B') (uni' : isFiberwiseUnivalent B' ρ') where

       ♭B' = ♭RelFamily B' (fst f)

       open RelIso

       RelFiberIsoOver→RelFiberIso : (e≅♭ : (a : A) → RelIso (B .snd {a = a}) (♭B' .snd {a = a}))
                                  → (a : A)
                                  → RelIso (B .snd {a = a}) (B' .snd {a = f .fst a})
       RelFiberIsoOver→RelFiberIso e≅♭ = e≅♭

       RelFiberIsoOver→FiberIso : (e≅♭ : (a : A) → RelIso (B .snd {a = a}) (♭B' .snd {a = a}))
                                  → (a : A)
                                  → Iso (B .fst a) (B' .fst (f .fst a))
       RelFiberIsoOver→FiberIso e≅♭ a = RelIso→Iso (snd B {a = a}) (snd B' {a = f .fst a}) ρ ρ' uni uni' (e≅♭ a)
-}
