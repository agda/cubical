{- Proof that containers are closed over least fixed points

Adapted from 'Containers: Constructing strictly positive types'
by Abbott, Altenkirch, Ghani

-}

{-# OPTIONS --safe #-}

open import Cubical.Data.W.W
open import Cubical.Data.Containers.Algebras
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude

module Cubical.Data.Containers.InductiveContainers
                           (Ind : Type)
                           (S : Type)
                           (P : Ind → S → Type)
                           (Q : S → Type)
                           (X : Ind → Type)
                           (Y : Type)
                           (α : Σ S (λ s → Σ ((i : Ind) → P i s → X i) (λ _ → Q s → Y)) → Y) where

  open Algs S Q

  into : Σ[ (s , f) ∈ Σ[ s ∈ S ] (Q s → W S Q) ]
           (((i : Ind) → P i s → X i) ×
           ((i : Ind) (q : Q s) → Pos P WAlg i (f q) → X i)) →
         Σ[ w ∈ W S Q ] ((i : Ind) → Pos P WAlg i w → X i)
  into ((s , f) , (g , h)) = sup-W s f , λ i → λ {(here p) → g i p ; (below q b) → h i q b}

  α̅' : (w : W S Q) → ((i : Ind) → Pos P WAlg i w → X i) → Y
  α̅' (sup-W s f) k = α (s , g , λ q → α̅' (f q)  (λ i → h i q))
    where
      g : (i : Ind) → P i s → X i
      g i p = k i (here p)

      h : (i : Ind) → (q : Q s) → Pos P WAlg i (f q) → X i
      h i q b = k i (below q b)

  α̅ : Σ[ w ∈ W S Q ] ((i : Ind) → Pos P WAlg i w → X i) → Y
  α̅ (w , k) = α̅' w k

  -- Diagram commutes
  α̅Comm : (s : S) (f : Q s → W S Q) (g : (i : Ind) → P i s → X i)
           (h : (i : Ind) (q : Q s) → Pos P WAlg i (f q) → X i) →
           α̅ (into ((s , f) , (g , h))) ≡ α (s , g , λ q → α̅ (f q , λ i → h i q))
  α̅Comm s f g h = refl

  -- α̅ is unique
  α̅Unique : (α̃ : Σ[ w ∈ W S Q ] ((i : Ind) → Pos P WAlg i w → X i) → Y) →
             ((s : S) (f : Q s → W S Q) (g : (i : Ind) → P i s → X i)
             (h : (i : Ind) (q : Q s) → Pos P WAlg i (f q) → X i) →
             α̃ (into ((s , f) , (g , h))) ≡ α (s , g , λ q → α̃ (f q , λ i → h i q))) →
             α̅ ≡ α̃
  α̅Unique α̃ α̃-comm = funExt w-rec
    where
      lemma : (s : S) (f : Q s → W S Q) (g : (i : Ind) → Pos P WAlg i (sup-W s f) → X i) →
              α̃ (into ((s , f) , (λ i p → g i (here p)) , (λ i q b → g i (below q b)))) ≡
              α̃ (sup-W s f , g)
      lemma s f g = cong₂ (λ w fun → α̃ (w , fun)) refl (funExt λ i → funExt (λ {(here p) → refl ; (below q b) → refl}))

      w-rec : (x : Σ[ w ∈ W S Q ] ((i : Ind) → Pos P WAlg i w → X i)) → α̅ x ≡ α̃ x
      w-rec (w , k) = WInd S Q
                         (λ w → (k : (i : Ind) → Pos P WAlg i w → X i) → α̅ (w , k) ≡ α̃ (w , k))
                         (λ {s'} {f'} ind k →
                           (λ i → α (s' , (λ i p → k i (here p)) ,
                                  λ q → ind q (λ i pos → k i (below q pos)) i)) ∙
                           sym (α̃-comm s' f' (λ i p → k i (here p))
                             (λ i q b → k i (below q b))) ∙
                           lemma s' f' k)
                         w k
