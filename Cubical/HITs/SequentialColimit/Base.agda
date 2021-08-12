{-# OPTIONS --safe #-}
{-
  This is based on the article by Sojakova, van Doorn and Rijke:
  https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf

  It seemed to be not worth the effort to join this with the colimits
  over a graph-shaped diagram
-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.SuccStr
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ′ : Level
    S : SuccStr ℓ

open SuccStr

data GenericSeqColimit (S : SuccStr ℓ) (s : TypeSeq ℓ′ S) : Type (ℓ-max ℓ ℓ′) where
    ι : (l : Index S) → fst s l → GenericSeqColimit S s
    glue : (l : Index S) (x : fst s l) → ι l x ≡ ι (succ S l) (snd s l x)

SeqColimit : (s : TypeSeq ℓ′ ℕ+) → Type _
SeqColimit = GenericSeqColimit ℕ+

NatTransform : (s : TypeSeq ℓ S) (s′ : TypeSeq ℓ′ S)
              → Type _
NatTransform {S = S} s s′ = Σ[ η ∈ ((n : Index S) → fst s n → fst s′ n) ]
                    ((n : Index S) → snd s′ n ∘ η n ≡ η (succ S n) ∘ snd s n)

InducedMap : {s : TypeSeq ℓ S} {s′ : TypeSeq ℓ′ S}
             (η : NatTransform s s′)
            → (GenericSeqColimit S s → GenericSeqColimit S s′)
InducedMap η (ι l x) = ι l (fst η l x)
InducedMap {S = S} {s = s} {s′ = s′} η (glue l x i) =
        (ι l (fst η l x)                            ≡⟨ glue l (fst η l x) ⟩
        ι (succ S l) (snd s′ l (fst η l x))         ≡[ j ]⟨ ι _ (snd η l j x) ⟩
        ι (succ S l) (fst η (succ S l) (snd s l x)) ∎) i

ShiftSeq : TypeSeq ℓ S → TypeSeq ℓ S
ShiftSeq {S = S} s = (λ n → fst s (succ S n)) , λ n → snd s (succ S n)

module Cofinality (s : TypeSeq ℓ ℕ+) where
    To : SeqColimit s → SeqColimit (ShiftSeq s)
    To (ι l x) = ι l (snd s l x)
    To (glue l x i) = glue l (snd s l x) i

    From : SeqColimit (ShiftSeq s) → SeqColimit s
    From (ι l x) = ι (suc l) x
    From (glue l x i) = glue (suc l) x i