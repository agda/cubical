{- Proof that containers are closed under greatest fixed points

Adapted from 'Containers: Constructing strictly positive types'
by Abbott, Altenkirch, Ghani

-}

{-# OPTIONS --safe --guardedness #-}

module Cubical.Codata.Containers.CoinductiveContainers where

open import Cubical.Codata.M.MRecord
open import Cubical.Codata.Containers.Coalgebras

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Containers.Algebras

open M
open M-R

module _ {ℓInd ℓS ℓP ℓQ ℓX ℓY : Level}
  (Ind : Type ℓInd)
  (S : Type ℓS)
  (P : Ind → S → Type ℓP)
  (Q : S → Type ℓQ)
  (X : Ind → Type ℓX)
  (Y : Type ℓY) where
  open Algs S Q
  open Coalgs S Q

  open FixedPoint
  open Iso

  out : Σ[ m ∈ M S Q ] ((i : Ind) → Pos P MAlg i m → X i) →
        Σ[ (s , f) ∈ Σ[ s ∈ S ] (Q s → M S Q) ]
          (((i : Ind) → P i s → X i) ×
          ((i : Ind) (q : Q s) → Pos P MAlg i (f q) → X i))
  out (m , k) = (shape m , pos m) , ((λ i p → k i (here p)) , (λ i q p → k i (below q p)))

  -- Construction of a generic
  -- β̅ : Y → Σ[ m ∈ M S Q ] ((i : Ind) → Pos P MAlg i m → X i)
  module β1 (βs : Y → S)
            (βh : (y : Y) → Q (βs y) → Y) where

    β̅₁ : Y → M S Q
    shape (β̅₁ y) = βs y
    pos (β̅₁ y) t = β̅₁ (βh y t)

    module β2 (βg : (y : Y) → (i : Ind) → P i (βs y) → X i) where
      β̅₂ : (y : Y) (ind : Ind) → Pos P MAlg ind (β̅₁ y) → X ind
      β̅₂ y ind (here p) = βg y ind p
      β̅₂ y ind (below q p) = β̅₂ (βh y q) ind p

      β̅ : Y → Σ[ m ∈ M S Q ] ((i : Ind) → Pos P MAlg i m → X i)
      β̅ y = β̅₁ y , β̅₂ y

      -- Diagram commutes
      β̅Comm : (y : Y) → out (β̅ y) ≡ ((βs y , β̅₁ ∘ (βh y)) , (βg y , λ i q → β̅₂ (βh y q) i))
      β̅Comm y = refl

  -- Characterisation of the equality type of the first projection of
  -- such a β̅
  module makeFirstEq
    (β̃₁ : Y → M S Q)
    (β̃₂ : (y : Y) (ind : Ind) → Pos P MAlg ind (β̃₁ y) → X ind)
    (βs : Y → S)
    (comm1 : (λ y → fst (fst (out (β̃₁ y , β̃₂ y)))) ≡ βs) --(comm1 : shape ∘ β̃₁ ≡ βs)
    (βh : (y : Y) → Q (βs y) → Y)
    (comm2 :  (y : Y) → PathP (λ i → Q (comm1 i y) → M S Q)
                              (λ q → snd (fst (out (β̃₁ y , β̃₂ y))) q) (λ q → β̃₁ (βh y q)))
    where
    open β1

    data R : M S Q → M S Q → Type (ℓ-max ℓS (ℓ-max ℓY ℓQ)) where
      R-intro : (y : Y) → R (β̃₁ y) (β̅₁ βs βh y)

    isBisimR : {m₀ : M S Q} {m₁ : M S Q} → R m₀ m₁ → M-R R m₀ m₁
    s-eq (isBisimR (R-intro y)) i = comm1 i y
    p-eq (isBisimR (R-intro y)) q₀ q₁ q-eq =
      transport (λ i → R (comm2 y (~ i) (q-eq (~ i)))
                (β̅₁ βs βh (βh y q₁)))
                (R-intro (βh y q₁))

    -- first main result
    preFstEq : (y : Y) → β̃₁ y ≡ β̅₁ βs βh y
    preFstEq y = MCoind R isBisimR (R-intro y)

    -- Because preFstEq is defined using MCoind, its proof term
    -- in the pos case is rather complicated. It _should_ look like this:
    preFstEq-pos : (y : Y)
      → PathP (λ i → Q (shape (preFstEq y i)) → M S Q)
               (pos (β̃₁ y)) (λ t → β̅₁ βs βh (βh y t))
    preFstEq-pos y i q =
      hcomp (λ j → λ { (i = i0) → pos (β̃₁ y) q ;
                       (i = i1) → preFstEq (βh y q) j })
            (comm2 y i q)
    -- but this definition is not accepted by the termination checker...

  -- Fortunately, we can prove that (cong pos ∘ preFstEq) and
  -- preFstEq-pos are equal up to a path (by J and some technical
  -- transport juggling).
  preFstEqId : (β̃₁ : Y → M S Q)
         (β̃₂ : (y : Y) (ind : Ind) → Pos P MAlg ind (β̃₁ y) → X ind)
         (βs : Y → S)
         (comm1 : shape ∘ β̃₁ ≡ βs)
         (βh : (y : Y) → Q (βs y) → Y)
         (comm2 : (y : Y) → PathP (λ i → Q (comm1 i y) → M S Q)
                                   (pos (β̃₁ y)) (λ q → β̃₁ (βh y q)))
         (y : _)
    → cong pos (makeFirstEq.preFstEq β̃₁ β̃₂ βs comm1 βh comm2 y)
     ≡ makeFirstEq.preFstEq-pos β̃₁ β̃₂ βs comm1 βh comm2 y
  preFstEqId β̃₁ β̃₂ =
    J> λ βh comm2 y
     → (λ j i q → MCoind (R βh comm2)
         (isBisimR βh comm2)
         {m₀ = pos (β̃₁ y) (transportRefl q (~ i ∨ j))}
         {m₁ = pos (β̅₁ ((λ r → shape r) ∘ β̃₁) βh y) (transportRefl q (i ∨ j))}
         ((p-eq (isBisimR βh comm2 (R-intro y))
         (transportRefl q (~ i ∨ j)) (transportRefl q (i ∨ j))
         λ k → transp (λ _ → Q (shape (β̃₁ y)))
                       (((~ k ∧ (~ i)) ∨ (k ∧ i)) ∨ j) q)) i)
        ∙ cong funExt (funExt λ q
       → lUnit _
       ∙ (λ j → (λ s → comm2 y (j ∧ s) q)
               ∙ MCoind {S = S} {Q = Q} (R βh comm2 )
                 (isBisimR βh comm2)
                 {m₀ = comm2 y j q}
                 {m₁ = pos (β̅₁ ((λ r → shape r) ∘ β̃₁) βh y) q}
                 (transp (λ i → R βh comm2 (comm2 y (~ i ∨ j) q)
                                   (β̅₁ ((λ r → shape r) ∘ β̃₁) βh (βh y q)))
                        j
                        (R-intro (βh y q)))))
    where
    open β1
    open makeFirstEq β̃₁ β̃₂ _ refl

  -- main part of the proof
  module _
    (βs : Y → S)
    (βh : (y : Y) → Q (βs y) → Y)
    (βg : (y : Y) → (i : Ind) → P i (βs y) → X i)
    (β̃₁ : Y → M S Q)
    (β̃₂ : (y : Y) (ind : Ind) → Pos P MAlg ind (β̃₁ y) → X ind)
    (βh : (y : Y) → Q (βs y) → Y)
    (comm1 : (y : Y) → fst (fst (out (β̃₁ y , β̃₂ y))) ≡ βs y)
    (comm2 :  (y : Y) → PathP (λ i → Q (comm1 y i) → M S Q)
                              (λ q → snd (fst (out (β̃₁ y , β̃₂ y))) q) (λ q → β̃₁ (βh y q)))
    (comm3 : (y : Y) → PathP (λ i → (ind : Ind) → P ind (comm1 y i) → X ind)
                             (fst (snd (out (β̃₁ y , β̃₂ y))))
                             (βg y))
    (comm4 : (y : Y) → PathP (λ i → (ind : Ind) → (q : Q (comm1 y i))
                     → Pos P MAlg ind (comm2 y i q) → X ind)
                         (snd (snd (out (β̃₁ y , β̃₂ y))))
                         (λ ind q b → (β̃₂ (βh y q)) ind b))
   where
     β̃ : Y → Σ[ m ∈ M S Q ] ((i : Ind) → Pos P MAlg i m → X i)
     β̃ y = β̃₁ y , β̃₂ y

     open β1 βs βh
     open β2 βg
     open makeFirstEq β̃₁ β̃₂ βs (funExt comm1) βh comm2

     fstEq : (y : Y) → β̃₁ y ≡ β̅₁ y
     fstEq = preFstEq

     sndEq : (y : Y)
       → PathP (λ i → (ind : Ind) → Pos P MAlg ind (fstEq y i) → X ind)
               (β̃₂ y) (β̅₂ y)
     sndEq y = funExt λ ind
       → toPathP (funExt λ x → transportRefl _
                               ∙ mainlem ind x)
       where
       module _ (ind : Ind) where
         mainlemHere : (t : Y) (x : P ind _)
           → β̃₂ t ind (subst (Pos P MAlg ind) (sym (fstEq t)) (here x))
            ≡ β̅₂ t ind (here x)
         mainlemHere y x =
           cong (β̃₂ y ind)
                (transportPresHere ind _ (sym (fstEq y)) _)
                ∙ funExtDep⁻ (funExt⁻ (comm3 y) ind)
            λ j → (transp (λ i → P ind (comm1 y (~ i ∨ j))) j x)

         mainlemBelow : (t : Y) (q : Q (βs t))
           (e : Pos P MAlg ind (β̅₁ (βh t q)))
          → β̃₂ (βh t q) ind
             (subst (Pos P MAlg ind) (sym (fstEq (βh t q))) (transport refl e))
           ≡ β̅₂ (βh t q) ind (transport refl e)
          → β̃₂ t ind (subst (Pos P MAlg ind) (sym (fstEq t))
                       (below q e))
            ≡ β̅₂ (βh t q) ind e
         mainlemBelow t q e indh =
             cong (β̃₂ t ind)
               (transportPresBelow ind _ _ _ e
               ∙ cong (below (subst (Q ∘ shape) (sym (fstEq t)) q))
                   (cong (λ p → subst (Pos P MAlg ind) p e)
                     (λ i j → comm2' i j)
                  ∙ moveTransp))
           ∙ comm4'
           ∙ ind'
           where
           comm2' : I → I → M S Q
           comm2' j i =
             hcomp (λ k
             → λ {(i = i0) → fstEq (βh t q) i1
                 ; (i = i1) → pos-t
                 ; (j = i1) → cpf i1 i
                ; (j = i0) → preFstEqId β̃₁ β̃₂ βs (funExt comm1) βh comm2 t
                              (~ k) (~ i)
                              (transp (λ i₁ → Q (comm1 t (~ i ∨ ~ i₁)))
                                      (~ i) q)})
              (hcomp (λ k
                → λ {(i = i0) → fstEq (βh t q) k
                   ; (i = i1) → pos-t
                   ; (j = i1) → cpf k i})
                (comm2 t (~ i)
                  (transp (λ i₁ → Q (comm1 t (~ i ∨ ~ i₁)))
                          (~ i)
                          q)))
             where
             pos-t = pos (β̃₁ t) (transport (sym (cong Q (comm1 t))) q)
             cpf = compPath-filler'
                   (sym (fstEq (βh t q)))
                   (sym (funExtDep⁻ (comm2 t)
                         (λ j₁ → transp (λ i₂ → Q (comm1 t (j₁ ∨ ~ i₂)))
                         j₁ q)))

           moveTransp =
             substComposite
              (Pos P MAlg ind)
              (sym (fstEq (βh t q)))
              (sym (funExtDep⁻ (comm2 t)
              (λ j → transp (λ i → Q (shape (fstEq t (j ∨ ~ i)))) j q))) e

           comm4' : _ ≡ β̃₂ (βh t q) ind
                      (subst (Pos P MAlg ind)
                        (sym (fstEq (βh t q))) e)
           comm4' =
               sym (transportRefl _)
             ∙ funExt⁻ (fromPathP (funExtDep⁻ (funExt⁻ (comm4 t) ind)
                       λ j → transp (λ i → Q (shape (fstEq t (j ∨ ~ i)))) j q))
                      (subst (Pos P MAlg ind) (λ i → fstEq (βh t q) (~ i)) e)

           ind' : β̃₂ (βh t q) ind
                   (subst (Pos P MAlg ind) (sym (fstEq (βh t q))) e)
               ≡ β̅₂ (βh t q) ind e
           ind' = cong (β̃₂ (βh t q) ind)
                    (cong (subst (Pos P MAlg ind) (sym (fstEq (βh t q))))
                      (sym (transportRefl e)))
                ∙∙ indh
                ∙∙ cong (β̅₂ (βh t q) ind) (transportRefl e)

         mainlem : (x : Pos P MAlg ind (β̅₁ y))
           → β̃₂ y ind  (transport (λ j → Pos P MAlg ind (fstEq y (~ j))) x)
            ≡ β̅₂ y ind x
         mainlem =
           PosIndFun P MAlg ind β̅₁ _ (λ t q → (βh t q) , refl)
                       mainlemHere mainlemBelow y

     -- β̅ makes the diagram commute uniquely
     β̅Unique : β̃ ≡ β̅
     fst (β̅Unique i y) = fstEq y i
     snd (β̅Unique i y) = sndEq y i
