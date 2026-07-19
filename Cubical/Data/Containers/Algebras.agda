{- Basic definitions required for co/inductive container proofs

- Definition of Pos

-}


module Cubical.Data.Containers.Algebras where

open import Cubical.Data.W.W
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module Algs (S : Type ℓ)
            (Q : S → Type ℓ') where

  open Iso

  -- Fixed point algebras
  record ContFuncIso : Type (ℓ-max (ℓ-suc ℓ'') (ℓ-max ℓ ℓ')) where
    constructor iso
    field
      carrier : Type ℓ''
      χ : Iso (Σ[ s ∈ S ] (Q s → carrier)) carrier

  open ContFuncIso

  WAlg : ContFuncIso
  WAlg = iso (W S Q) isom
    where
      isom : Iso (Σ[ s ∈ S ] (Q s → W S Q)) (W S Q)
      fun isom = uncurry sup-W
      inv isom (sup-W s f) = s , f
      rightInv isom (sup-W s f) = refl
      leftInv isom (s , f) = refl

  data Pos {Ind : Type ℓ'''} (P : Ind → S → Type ℓ'') (FP : ContFuncIso {ℓ}) (i : Ind) :
           carrier FP → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ'' ℓ')) where
    here : {wm : carrier FP} → P i (fst (FP .χ .inv wm)) → Pos P FP i wm
    below : {wm : carrier FP} → (q : Q (fst (FP .χ .inv wm))) →
            Pos P FP i (snd (FP .χ .inv wm) q) → Pos P FP i wm
