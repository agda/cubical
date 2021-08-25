{-# OPTIONS --safe #-}
{-
  This is based on the article by Sojakova, van Doorn and Rijke:
  https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf

-}
module Cubical.HITs.SequentialColimit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws


open import Cubical.HITs.SequentialColimit.Base 

open import Cubical.Data.SuccStr
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ′ : Level
    S : SuccStr ℓ

open SuccStr

{-
    This is about the property, that the colimit does not change,
    if some finite beginning of the sequence is removed.
-}
module Cofinality (s : TypeSeq ℓ ℕ+) where
    To : SeqColimit s → SeqColimit (ShiftedSeq s 1)
    To (ι l x) = ι l (snd s l x)
    To (glue l x i) = glue l (snd s l x) i

    From : SeqColimit (ShiftedSeq s 1) → SeqColimit s
    From (ι l x) = ι (suc l) x
    From (glue l x i) = glue (suc l) x i

    ToFrom : (x : SeqColimit (ShiftedSeq s 1)) → x ≡ To (From x)
    ToFrom (ι l x) = glue l x
    ToFrom (glue l x i) j = square i j
           where  g1 : ι l  x ≡ ι (suc l) (snd (ShiftedSeq s 1) l x)
                  g1 = glue l x
                  g2 : _ ≡ ι _ (snd (ShiftedSeq s 1) _ (snd (ShiftedSeq s 1) l x))
                  g2 = glue (suc l) (snd (ShiftedSeq s 1) l x)
                  square : Square g1 g2 g1 g2
                  square = compositionReflSquare g1 g2

    FromTo : (x : SeqColimit s) → x ≡ From (To x)
    FromTo (ι l x) = glue l x
    FromTo (glue l x i) j = square i j
            where  g1 : ι l x ≡ ι (suc l) (snd s l x)
                   g1 = glue l x
                   g2 : _ ≡ _
                   g2 = glue (suc l) (snd s l x)
                   square : Square g1 g2 g1 g2
                   square = compositionReflSquare g1 g2

ShiftSeqColimit : (s : TypeSeq ℓ ℕ+) (n : ℕ) 
                    → SeqColimit s → SeqColimit (ShiftedSeq s n)
ShiftSeqColimit s zero = λ x → x
ShiftSeqColimit s (suc n) = Cofinality.To (ShiftedSeq s n) ∘ ShiftSeqColimit s n

{- Lemma 3.7 in the paper -}
ShiftEquiv : (s : TypeSeq ℓ ℕ+) (n : ℕ)
            → SeqColimit s ≃ SeqColimit (ShiftedSeq s n)
ShiftEquiv s zero = ShiftSeqColimit s zero , idIsEquiv _
ShiftEquiv s (suc n) = 
    compEquiv 
        (ShiftEquiv s n) 
        (isoToEquiv (iso (Cofinality.To seq) (Cofinality.From seq) 
                         (λ x → sym (Cofinality.ToFrom seq x)) 
                         λ y → sym (Cofinality.FromTo seq y)))
    where seq = ShiftedSeq s n
