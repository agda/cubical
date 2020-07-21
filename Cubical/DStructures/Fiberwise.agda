
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓ≅A ℓ≅B ℓ≅C ℓ≅B' : Level

module Fib1 {A : Type ℓA} {B : A → Type ℓB} {C : A → Type ℓC} where

  -- this belongs in Relation/Binary
  -- the notion of a fiberwise isomorphism with respect to a binary relation
  record FiberRelIso (_≅B_ : {a : A} → Rel (B a) (B a) ℓ≅B)
                     (_≅C_ : {a : A} → Rel (C a) (C a) ℓ≅C) : Type (ℓ-max (ℓ-max ℓA (ℓ-max ℓB ℓC)) (ℓ-max ℓ≅B ℓ≅C)) where
    constructor fiberRelIso
    field
      fun : {a : A} → B a → C a
      inv : {a : A} → C a → B a
      sec : {a : A} → (c : C a) → fun (inv c) ≅C c
      ret : {a : A} → (b : B a) → inv (fun b) ≅B b

  module _ {StrA : URGStr A ℓ≅A} {StrBᴰ : URGStrᴰ StrA B ℓ≅B} {StrCᴰ : URGStrᴰ StrA C ℓ≅C} where
    -- maybe put this into separate module that exports useful notation
    module _ where
      ρ = URGStr.ρ StrA
      ρB = URGStrᴰ.ρᴰ StrBᴰ
      ρC = URGStrᴰ.ρᴰ StrCᴰ

      _≅B_ : {a : A} → Rel (B a) (B a) ℓ≅B
      _≅B_ {a} b b' = URGStrᴰ._≅ᴰ⟨_⟩_ StrBᴰ b (ρ a) b'
      _≅C_ : {a : A} → Rel (C a) (C a) ℓ≅C
      _≅C_ {a} c c' = URGStrᴰ._≅ᴰ⟨_⟩_ StrCᴰ c (ρ a) c'

      -- combine univalence map and proof that it is an equivalence
      -- to be able to invert it
      uniB : {a : A} (b b' : B a) → (b ≡ b') ≃ (b ≅B b')
      uniB b b' = ≡→R _≅B_ ρB , URGStrᴰ.uniᴰ StrBᴰ b b'

      uniC : {a : A} (c c' : C a) → (c ≡ c') ≃ (c ≅C c')
      uniC c c' = ≡→R _≅C_ ρC , URGStrᴰ.uniᴰ StrCᴰ c c'

    -- use univalence of the graph structure to show that
    -- fiberwise relational isos are fiberwise isos
    DispFiberIso→FiberEquiv : ((fiberRelIso F G FG GF) : FiberRelIso _≅B_ _≅C_)
                              → (a : A)
                              → Iso (B a) (C a)
    DispFiberIso→FiberEquiv (fiberRelIso F G FG GF) a
      = iso (F {a})
            (G {a})
            (λ c → (invEquiv (uniC (F (G c)) c)) .fst (FG c))
            λ b → (invEquiv (uniB (G (F b)) b)) .fst (GF b)

module Fib2 {A : Type ℓA} {A' : Type ℓA'} (f : A → A')
            {B' : A' → Type ℓB'} where

  module _ {ℓ≅B' : Level} (_≅B'_ : {a : A'} → Rel (B' a) (B' a) ℓ≅B') where
    -- pull back fiber relation
    ♭FiberRel : Σ[ ♭B' ∈ (A → Type ℓB') ] ({a : A} → Rel (♭B' a) (♭B' a) ℓ≅B')
    fst ♭FiberRel a = B' (f a)
    snd ♭FiberRel = _≅B'_

    private
      ♭B' = fst ♭FiberRel
      _≅♭B'_ = snd ♭FiberRel

    module _ {B : A → Type ℓB} where
      -- definition of fiberwise relational iso with respect to the map f
      record FiberRelIso {ℓ≅B : Level} (_≅B_ : {a : A} → Rel (B a) (B a) ℓ≅B) : Type (ℓ-max (ℓ-max ℓ≅B ℓ≅B') (ℓ-max ℓA (ℓ-max ℓB ℓB'))) where
        constructor fiberreliso
        field
          fun : {a : A} → B a → ♭B' a
          inv : {a : A} → ♭B' a → B a
          sec : {a : A} → (b' : ♭B' a) → fun (inv b') ≅♭B' b'
          ret : {a : A} → (b : B a) → inv (fun b) ≅B b
