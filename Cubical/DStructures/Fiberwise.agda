
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
    ℓA ℓB ℓC ℓ≅A ℓ≅B ℓ≅C : Level

module _ {A : Type ℓA} {B : A → Type ℓB} {C : A → Type ℓC} where

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
