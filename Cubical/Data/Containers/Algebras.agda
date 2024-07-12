{- Basic definitions required for co/inductive container proofs

- Definition of Pos
- Elimination principle

-}

{-# OPTIONS --safe #-}

module Cubical.Data.Containers.Algebras where

open import Cubical.Data.W.W
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
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

  data Pos {ℓ ℓ'' ℓ'''} {Ind : Type ℓ'''}
           (P : Ind → S → Type ℓ'') (FP : ContFuncIso {ℓ}) (i : Ind) :
           carrier FP → Type (ℓ-max (ℓ-suc ℓ''') (ℓ-max ℓ'' (ℓ-max ℓ' ℓ))) where
    here : {wm : carrier FP} (r : P i (fst (FP .χ .inv wm))) → Pos P FP i wm
    below : {wm : carrier FP} (q : Q (fst (FP .χ .inv wm)))
          → Pos P FP i (snd (FP .χ .inv wm) q) → Pos P FP i wm

  -- Height of an element of pos
  heightPos : ∀ {ℓInd ℓP ℓFP} {Ind : Type ℓInd} {P : Ind → S → Type ℓP}
      {FP : ContFuncIso {ℓFP}} {i : Ind} {wm : _}
    → Pos P FP i wm → ℕ
  heightPos (here r) = 0
  heightPos (below q x) = suc (heightPos x)

  -- Elimination principle for Pos P FP i (β y)
  -- where β : Y → carrier FP
  pos-rec-fun : ∀ {ℓY ℓInd ℓW ℓFP} {Y : Type ℓY} {Ind : Type ℓInd}
    (P : Ind → S → Type ℓ'')
    (FP : ContFuncIso {ℓFP}) (i : Ind)
    (β : Y → carrier FP)
    (W : (y : Y) → Pos P FP i (β y) → Type ℓW)
    (βid : (t : Y) (q : Q (fst (FP .χ .inv (β t)))) -- additional assumption: β is nice
       → Σ[ t' ∈ Y ] ((snd (FP .χ .inv (β t)) q) ≡ β t'))
    (here* : (t : Y) (x : P i (fst (FP .χ .inv (β t)))) → W t (here x))
    (below* : (t : Y) (q : Q (fst (FP .χ .inv (β t))))
              (e : Pos P FP i (snd (FP .χ .inv (β t)) q))
           → W _ (subst (Pos P FP i) (βid t q .snd) e)
           → W t (below q e))
    (t : Y) (e : Pos P FP i (β t)) → W t e
  pos-rec-fun {Ind} P FP i β W βid non non2 t e =
    pos-rec-fun-help _ t e refl
    where
    pos-rec-fun-help :
      (n : ℕ)
      (t : _) (e : Pos P FP i (β t))
      → heightPos e ≡ n
      → W t e
    pos-rec-fun-help zero t (here r) p = non t r
    pos-rec-fun-help zero t (below q e) p = ⊥.rec (snotz p)
    pos-rec-fun-help (suc n) t (here r) p = ⊥.rec (snotz (sym p))
    pos-rec-fun-help (suc n) t (below q e) p =
      non2 t q e
        (pos-rec-fun-help n
          _ (subst (Pos P FP i) (βid t q .snd) e)
            (substPresHeight _ _ ∙ cong predℕ p))
      where
      substPresHeight : (b : _) (p : _ ≡ b)
        → heightPos (subst (Pos P FP i) p e)  ≡ heightPos e
      substPresHeight = J> cong heightPos (transportRefl e)


  -- transport preserves here and below
  module _ {ℓ ℓ'' ℓ''' : Level} {Ind : Type ℓ'''}
           {P : Ind → S → Type ℓ''}
           {FP : ContFuncIso {ℓ}} (i : Ind) where

     transportPresHere : {a : _} (b : _) (p : a ≡ b) (x : _)
       → subst (Pos P FP i) p (here x)
        ≡ here (subst (P i ∘ fst ∘ (FP .χ .inv)) p x)
     transportPresHere =
       J> λ x → transportRefl (here x)
               ∙ cong here (sym (transportRefl _))

     transportPresBelow : {a : _} (b : _) (p : a ≡ b) (q : _) (x : _)
       → subst (Pos P FP i) p (below q x)
        ≡ below (subst (Q ∘ fst ∘ (FP .χ .inv)) p q)
                 (subst (Pos P FP i)
                        (λ j → snd (FP .χ .inv (p j))
                          (transp (λ i → Q (fst (FP .χ .inv (p (j ∧ i)))))
                                  (~ j) q))
                        x)
     transportPresBelow =
       J> λ q x → transportRefl (below q x)
                ∙ cong₂ below (sym (transportRefl q))
                    (toPathP refl)
