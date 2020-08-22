{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base



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

module _ {A : Type ℓA} {A' : Type ℓA'} (F : Iso A A')
         (ℬ : RelFamily A ℓB ℓ≅B) {ρ : isFiberwiseReflexive ℬ} (uni : isFiberwiseUnivalent ℬ ρ)
         (ℬ' : RelFamily A' ℓB' ℓ≅B') {ρ' : isFiberwiseReflexive ℬ'} (uni' : isFiberwiseUnivalent ℬ' ρ') where

       private
         f = Iso.fun F
         B = ℬ .fst
         B' = ℬ' .fst
         ♭B' = ♭RelFamily ℬ' f .fst
         ♭ℬ' = ♭RelFamily ℬ' f

       private
         RelFiberIsoOver→♭FiberIso : (e≅♭ : (a : A) → RelIso (ℬ .snd {a = a}) (♭ℬ' .snd {a = a}))
                                     → (a : A)
                                     → Iso (B a) (B' (f a))
         RelFiberIsoOver→♭FiberIso e≅♭ a = RelIso→Iso (ℬ .snd {a = a}) (ℬ' .snd {a = f a}) uni uni' (e≅♭ a)

       RelFiberIsoOver→Iso : (e≅♭ : (a : A) → RelIso (ℬ .snd {a = a}) (♭ℬ' .snd {a = a}))
                             → Iso (Σ A B) (Σ A' B')
       RelFiberIsoOver→Iso e≅♭ = Σ-cong-iso F (RelFiberIsoOver→♭FiberIso e≅♭)




-- old stuff

{-
record RelIsoOver {A : Type ℓA} {_≅A_ : Rel A A ℓ≅A}
                  {A' : Type ℓA'} {_≅A'_ : Rel A' A' ℓ≅A'}
                  (ℱ : RelIso _≅A_ _≅A'_)
                  (ℬ : RelFamily A ℓB ℓ≅B)
                  (ℬ' : RelFamily A' ℓB' ℓ≅B') : Type {!!} where

  private
    F = RelIso.fun ℱ
    F- = RelIso.inv ℱ
    B = λ (a : A) → ℬ .fst a
    B' = λ (a' : A') → ℬ' .fst a'

  field
    fun : {a : A} (b : B a) → B' (F a)
    inv : {a' : A'} (b' : B' a') → B (F- a')
    -- leftInv : {a : A} (b : B a) → inv (fun b) = b
    -- rightInv : {a' : A'} (b' : B' a') → fun (inv b') = b'
-}
