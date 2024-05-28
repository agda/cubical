{- Proof that containers are closed under greatest fixed points

Adapted from 'Containers: Constructing strictly positive types'
by Abbott, Altenkirch, Ghani

-}

{-# OPTIONS --without-K --guardedness --cubical #-}

open import Cubical.Codata.M.MRecord
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Containers.Algebras
open M'
open M'-R

module Cubical.Data.Containers.CoinductiveContainers
         (Ind : Type)
         (S : Type)
         (setS : isSet S)
         (P : Ind → S → Type)
         (Q : S → Type)
         (setM : isSet S → isSet (M' S Q))
         (X : Ind → Type)
         (Y : Type)
         (βs : Y → S)
         (βg : (y : Y) → (i : Ind) → P i (βs y) → X i)
         (βh : (y : Y) → Q (βs y) → Y) where
         
    open Algs Ind S P Q X Y

    β̅₁ : Y → M' S Q
    shape (β̅₁ y) = βs y
    pos (β̅₁ y) = β̅₁ ∘ βh y

    β̅₂ : (y : Y) (ind : Ind) → Pos MAlg ind (β̅₁ y) → X ind
    β̅₂ y ind (here p) = βg y ind p
    β̅₂ y ind (below q p) = β̅₂ (βh y q) ind p

    β̅ : Y → Σ[ m ∈ M' S Q ] ((i : Ind) → Pos MAlg i m → X i)
    β̅ y = β̅₁ y , β̅₂ y
    
    out : Σ[ m ∈ M' S Q ] ((i : Ind) → Pos MAlg i m → X i) →
          Σ[ (s , f) ∈ Σ[ s ∈ S ] (Q s → M' S Q) ]
            (((i : Ind) → P i s → X i) ×
            ((i : Ind) (q : Q s) → Pos MAlg i (f q) → X i))
    out (m , k) = (shape m , pos m) , ((λ i p → k i (here p)) , (λ i q p → k i (below q p)))

    module _ (β̃₁ : Y → M' S Q)
             (β̃₂ : (y : Y) (ind : Ind) → Pos MAlg ind (β̃₁ y) → X ind)
             (comm : (y : Y) →
                     out (β̃₁ y , β̃₂ y) ≡
                     ((βs y , λ q → (β̃₁ (βh y q))) , (βg y , λ i q → (β̃₂ (βh y q)) i))) where

      -- Diagram commutes
      β̅-comm : (y : Y) → out (β̅ y) ≡ ((βs y , β̅₁ ∘ (βh y)) , (βg y , λ i q → β̅₂ (βh y q) i))
      β̅-comm y = refl

      β̃ : Y → Σ (M' S Q) (λ m → (i : Ind) → Pos MAlg i m → X i)
      β̃ y = β̃₁ y , β̃₂ y

      ----------

      comm1 : (y : Y) → shape (β̃₁ y) ≡ shape (β̅₁ y)
      comm1 y i = fst (fst (comm y i))

      comm2 : (y : Y) →
                   PathP (λ i → Q (comm1 y i) → M' S Q)
                         (pos (β̃₁ y)) (λ q → β̃₁ (βh y q))
      comm2 y i = snd (fst (comm y i))

      comm3 : (y : Y) → PathP (λ i → (ind : Ind) → P ind (comm1 y i) → X ind)
                              (λ ind p → β̃₂ y ind (here p))
                              (βg y)
      comm3 y i = fst (snd (comm y i))

      comm4 : (y : Y) → PathP (λ i → (ind : Ind) → (q : Q (comm1 y i)) →
                              Pos MAlg ind (comm2 y i q) → X ind)
                              (λ ind q b → β̃₂ y ind (below q b))
                              (λ ind q b → β̃₂ (βh y q) ind b)
      comm4 y i = snd (snd (comm y i))

      data R : M' S Q → M' S Q → Type where
        R-intro : (y : Y) → R (β̃₁ y) (β̅₁ y)

      is-bisim-R : {m₀ : M' S Q} {m₁ : M' S Q} → R m₀ m₁ → M'-R R m₀ m₁
      s-eq (is-bisim-R (R-intro y)) = comm1 y
      p-eq (is-bisim-R (R-intro y)) q₀ q₁ q-eq = 
        transport (λ i → R (comm2 y (~ i) (q-eq (~ i))) (β̅₁ (βh y q₁))) (R-intro (βh y q₁))

      fst-eq : (y : Y) → β̃₁ y ≡ β̅₁ y
      fst-eq y = CoInd-M' {S} {Q} R is-bisim-R (R-intro y)

      snd-eq-gen : (y : Y) (β̃₁ : Y → M' S Q) (p : β̅₁ ≡ β̃₁)
                   (β̃₂ : (y : Y) (ind : Ind) → Pos MAlg ind (β̃₁ y) → X ind)
                   (comm1 : shape ∘ β̃₁ ≡ βs)
                   (comm2 : (y : Y) → PathP (λ i → Q (comm1 i y) → M' S Q)
                                            (pos (β̃₁ y)) (β̃₁ ∘ βh y))
                   (comm3 : (y : Y) → PathP (λ i  → (ind : Ind) → P ind (comm1 i y) → X ind)
                                            (λ ind p → β̃₂ y ind (here p))
                                            (βg y))
                   (comm4 : (y : Y) → PathP (λ i → (ind : Ind) (q : Q (comm1 i y)) →
                                            Pos MAlg ind (comm2 y i q) → X ind)
                                            (λ ind q b → β̃₂ y ind (below q b))
                                            λ ind q b → β̃₂ (βh y q) ind b) →
                   PathP (λ i → (ind : Ind) → Pos MAlg ind (p i y) → X ind)
                         (β̅₂ y) (β̃₂ y)
      snd-eq-gen y =
        J>_ -- we're applying J to p : makeβ̅₁ βs βg βh ≡ β̅₁
          {P = λ β̃₁ p →
            (β̃₂ : (y : Y) (ind : Ind) → Pos MAlg ind (β̃₁ y) → X ind)
            (comm1 : shape ∘ β̃₁ ≡ βs)
            (comm2 : (y : Y) → PathP (λ i → Q (comm1 i y) → M' S Q) (pos (β̃₁ y)) (β̃₁ ∘ βh y))
            (comm3 : (y : Y) → PathP (λ i  → (ind : Ind) → P ind (comm1 i y) → X ind)
                     (λ ind p → β̃₂ y ind (here p))
                     (βg y))
            (comm4 : (y : Y) → PathP (λ i → (ind : Ind) (q : Q (comm1 i y)) → Pos MAlg ind
                               (comm2 y i q) → X ind)
                     (λ ind q b → β̃₂ y ind (below q b))
                     λ ind q b → β̃₂ (βh y q) ind b) →
            PathP (λ i → (ind : Ind) → Pos MAlg ind (p i y) → X ind)
            (β̅₂ y) 
            (β̃₂ y)}
          λ β̃₂ comm1 →
            prop-elim -- S is a set so equality on S is a prop
              {A = (λ y → βs y) ≡ βs}
              (isSetΠ (λ _ → setS) (λ y → βs y) βs)
              (λ s-eq →
                (comm2 : (y : Y) → PathP (λ i → Q (s-eq i y) → M' S Q)
                                   (β̅₁ ∘ βh y) (β̅₁ ∘ βh y))
                (comm3 : (y : Y) → PathP (λ i  → (ind : Ind) → P ind (s-eq i y) → X ind)
                                   (λ ind p → β̃₂ y ind (here p)) (βg y))
                (comm4 : (y : Y) → PathP (λ i → (ind : Ind) (q : Q (s-eq i y)) → Pos MAlg ind
                                   (comm2 y i q) → X ind)
                                   (λ ind q b → β̃₂ y ind (below q b))
                                   (λ ind q b → β̃₂ (βh y q) ind b)) →
                         (β̅₂ y) ≡ (β̃₂ y))
              refl
              (prop-elim -- M' is a set so equality on M' is a prop
                {A = (y : Y) →
                     (λ x → β̅₁ (βh y x)) ≡ (λ x → β̅₁ (βh y x))}
                (isPropΠ λ y' → isSetΠ (λ _ → setM setS) (β̅₁ ∘ βh y') (β̅₁ ∘ βh y'))
                (λ m-eq → 
                  (comm3 : (y : Y) → (λ ind p → β̃₂ y ind (here p)) ≡ (βg y))
                  (comm4 : (y : Y) → PathP (λ i → (ind : Ind) (q : Q (βs y)) → Pos MAlg ind
                                     (m-eq y i q) → X ind)
                                     (λ ind q b → β̃₂ y ind (below q b))
                                     (λ ind q b → β̃₂ (βh y q) ind b)) →
                         (β̅₂ y) ≡ (β̃₂ y))
                (λ _ → refl)
                λ comm3 comm4 → funExt (λ ind → funExt (snd-eq-aux β̃₂ comm3 comm4 y ind)))
              comm1
        where
          snd-eq-aux : (β̃₂ : (s : Y) (i : Ind) → Pos MAlg i (β̅₁ s) → X i)
                       (c3 : (s : Y) → (λ ind p → β̃₂ s ind (here p)) ≡ βg s)
                       (c4 : (s : Y) → (λ ind q b → β̃₂ s ind (below q b)) ≡
                                       (λ ind q → β̃₂ (βh s q) ind))
                       (y : Y) (ind : Ind) (pos : Pos MAlg ind (β̅₁ y)) → β̅₂ y ind pos ≡ β̃₂ y ind pos
          snd-eq-aux β̃₂ c3 c4 y ind (here x) = sym (funExt⁻ (funExt⁻ (c3 y) ind) x)
          snd-eq-aux β̃₂ c3 c4 y ind (below q x) =
            snd-eq-aux β̃₂ c3 c4 (βh y q) ind x ∙ funExt⁻ (funExt⁻ (sym (funExt⁻ (c4 y) ind)) q) x

      snd-eq : (y : Y) → PathP (λ i → (ind : Ind) → Pos MAlg ind (fst-eq y i) → X ind) (β̃₂ y) (β̅₂ y)
      snd-eq y i = snd-eq-gen y β̃₁ (sym (funExt fst-eq)) β̃₂ (funExt comm1) comm2 comm3 comm4 (~ i)

      -- β̅ is unique
      β̅-unique : β̃ ≡ β̅
      fst (β̅-unique i y) = fst-eq y i
      snd (β̅-unique i y) = snd-eq y i

