{-# OPTIONS --safe #-}
{-
  This is based on the article by Sojakova, van Doorn and Rijke:
  https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf

-}
module Cubical.HITs.SequentialColimit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.SequentialColimit.Base 

open import Cubical.Data.SuccStr
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ′ : Level
    S : SuccStr ℓ

open SuccStr

module Cofinality (s : TypeSeq ℓ ℕ+) where
    To : SeqColimit s → SeqColimit (ShiftSeq s)
    To (ι l x) = ι l (snd s l x)
    To (glue l x i) = glue l (snd s l x) i

    From : SeqColimit (ShiftSeq s) → SeqColimit s
    From (ι l x) = ι (suc l) x
    From (glue l x i) = glue (suc l) x i

    ToFrom : (x : SeqColimit (ShiftSeq s)) → x ≡ To (From x)
    ToFrom (ι l x) = glue l x
    ToFrom (glue l x i) j = square i j
           where  g1 : ι l  x ≡ ι (suc l) (snd (ShiftSeq s) l x)
                  g1 = glue l x
                  g2 : _ ≡ ι _ (snd (ShiftSeq s) _ (snd (ShiftSeq s) l x))
                  g2 = glue (suc l) (snd (ShiftSeq s) l x)
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
