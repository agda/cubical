{-# OPTIONS --safe #-}
{-
  This is based on the article by Sojakova, van Doorn and Rijke:
  https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf

-}
module Cubical.HITs.SequentialColimit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.SequentialColimit.Base

open import Cubical.Data.SuccStr
open import Cubical.Data.Nat

open SuccStr

private
  variable
    ℓ ℓ′ : Level
    S : SuccStr ℓ
    i : index S

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

{- Induction data for sequential colimits -}
module _ {S : SuccStr ℓ′}  where
  IndData : (s : TypeSeq ℓ S) → Type _
  IndData {ℓ = ℓ} s = Σ[ B ∈ ((i : index S) → (x : fst s i) → Type ℓ) ]
            ((i : index S) → (x : fst s i) → B i x → B (succ S i) (snd s i x))

  ShiftedIndData : (s : TypeSeq ℓ S) → IndData s → IndData (ShiftedSeq s 1)
  ShiftedIndData s (fib , map) = {!   !}

{- Ingrdients for the main theorem (5.1) -}
module _ {S : SuccStr ℓ′} (s : TypeSeq ℓ S) (ind : IndData s) where
  {-
    Summing a dependent type over a sequence,
    gives a sequence of types.
  -}
  ΣSeqFromIndData : TypeSeq ℓ S
  ΣSeqFromIndData =
    (λ i → Σ[ x ∈ fst s i ] fst ind i x) ,
    (λ i → λ { (x , b) → (snd s i x) , (snd ind i x b) })

  {-
    An induction datum yields an ℕ-indexed type sequence for any index
    and point in the base. This is described and used on page 2 of the
    paper.
  -}
  SeqAt : {i : index S} (x : fst s i) → TypeSeq ℓ ℕ+
  SeqAt x = seq , op
          where seq : ℕ → _
                seq n = fst ind (TimesSucc n S _) (TimesSeqOp n s x)
                op : (n : ℕ) → seq n → seq (suc n)
                op n = snd ind (TimesSucc n S _) (TimesSeqOp n s x)

  ColimSeqAt : {i : index S} (x : fst s i) → Type ℓ
  ColimSeqAt x = SeqColimit (SeqAt x)


module _ {S : SuccStr ℓ′} (s : TypeSeq ℓ S) (ind : IndData s) where
  private
    SeqAtCommShift : {j : index S} (x : fst s j)
            → ShiftedSeq (SeqAt s ind x) 1 ≡ SeqAt (ShiftedSeq s 1) (ShiftedIndData s ind) (snd s j x)
    SeqAtCommShift  x i = fstEq i , sndEq i
        where fstEq : fst (ShiftedSeq (SeqAt s ind x) 1) ≡ fst (SeqAt (ShiftedSeq s 1) (ShiftedIndData s ind) (snd s _ x))
              fstEq i zero = fst ind _ (snd s _ x)
              fstEq i (suc n) = (
                fst (SeqAt s ind x) (suc (suc n))                                           ≡⟨ refl ⟩
                fst ind (succ S (TimesSucc (suc n) S _)) (snd s _ (TimesSeqOp (suc n) s x)) ≡⟨ {!  !} ⟩
                fst ind (TimesSucc (suc n) S (succ S _)) (TimesSeqOp (suc n) s (snd s _ x)) ≡⟨ refl ⟩
                fst (SeqAt (ShiftedSeq s 1) (ShiftedIndData s ind) (snd s _ x)) (suc n) ∎) i

              sndEq : PathP (λ i → (n : ℕ) → fstEq i n → fstEq i (suc n))
                            (snd (ShiftedSeq (SeqAt s ind x) 1))
                            (snd (SeqAt (ShiftedSeq s 1) (ShiftedIndData s ind) (snd s _ x)))
              sndEq i zero = {!  !}  -- snd (ShiftedSeq (SeqAt x) 1) zero
              sndEq i (suc n) = {!   !}
{-
  EquivColimSeq : {i : index S} (x : fst s i)
                  → ColimSeqAt x ≃ ColimSeqAt (snd s i x)
  EquivColimSeq x =
    ColimSeqAt x                         ≃⟨ ShiftEquiv (SeqAt x) 1 ⟩
    SeqColimit (ShiftedSeq (SeqAt x) 1)  ≃⟨ pathToEquiv (λ i → SeqColimit (SeqAtCommShift x i)) ⟩
    ColimSeqAt (snd s _ x) ■
-}