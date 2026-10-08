{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.FiberOrCofiberSequences.ChainOfFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.PuppeLemma

private
  variable
    ℓ : Level

mutual
  ChainOfFibersVertices : {A B C : Pointed ℓ} → FiberSeq A B C → ℕ → Pointed ℓ
  ChainOfFibersVertices {C = C} F 0 = C
  ChainOfFibersVertices {B = B} F 1 = B
  ChainOfFibersVertices {A = A} F 2 = A
  ChainOfFibersVertices F (suc 2) = fiber∙ (FiberSeqIncl F)
  ChainOfFibersVertices {A = A} {B = B} {C = C} F (suc (suc (suc (suc  n)))) =
    fiber∙ { A = ChainOfFibersVertices F (suc (suc (suc n)))}
           { B = ChainOfFibersVertices {A = A} {B = B} {C = C} F (suc (suc n))}
           ( ChainOfFibersEdges F (suc (suc n)))

  ChainOfFibersEdges : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ) →
             (ChainOfFibersVertices F (suc n)) →∙ (ChainOfFibersVertices F n)
  ChainOfFibersEdges F 0 = FiberSeqProj F
  ChainOfFibersEdges F 1 = FiberSeqIncl F
  ChainOfFibersEdges F 2 = fst , refl
  ChainOfFibersEdges F (suc (suc (suc n))) =
    fst , refl {x = snd (ChainOfFibersVertices F (suc (suc (suc n))))}

ChainOfFibers→FiberSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → FiberSeq ( ChainOfFibersVertices F (2 + n))
              ( ChainOfFibersVertices F (suc n))
              ( ChainOfFibersVertices F n)
ChainOfFibers→FiberSeq F zero = F
ChainOfFibers→FiberSeq F 1 = FiberFiberSeq (FiberSeqIncl F)
ChainOfFibers→FiberSeq F (suc (suc n)) =
  FiberFiberSeq (ChainOfFibersEdges F (2 + n))

ChainOfFibers→FiberSeqIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → FiberSeqIncl (ChainOfFibers→FiberSeq F n)
   ≡ ChainOfFibersEdges F (suc n)
ChainOfFibers→FiberSeqIncl F 0 = refl
ChainOfFibers→FiberSeqIncl F 1 = InclOfFiberFiberSeq (FiberSeqIncl F)
ChainOfFibers→FiberSeqIncl F (suc (suc n)) = InclOfFiberFiberSeq (ChainOfFibersEdges F (suc (suc n)))

ChainOfFibers→FiberSeqProj : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → FiberSeqProj (ChainOfFibers→FiberSeq F n)
  ≡ ChainOfFibersEdges F n
ChainOfFibers→FiberSeqProj F 0 = refl
ChainOfFibers→FiberSeqProj F 1 = ProjOfFiberFiberSeq (FiberSeqIncl F)
ChainOfFibers→FiberSeqProj F (suc (suc n)) = ProjOfFiberFiberSeq (ChainOfFibersEdges F (suc (suc n)))

LoopSpacesInChainOfFibers : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → ChainOfFibersVertices F (3 + n) ≡ Ω (ChainOfFibersVertices F n)
LoopSpacesInChainOfFibers F zero =
  fst (PathPΣ (FibsEqOfFibSeq
               ( ChainOfFibers→FiberSeq F 1)
               ( puppe (ChainOfFibers→FiberSeq F 0))
               ( ProjOfFiberFiberSeq (FiberSeq.incl F) ∙ puppeProjEqFibIncl F ⁻¹)))
LoopSpacesInChainOfFibers F 1 =
  fst (PathPΣ (FibsEqOfFibSeq
               ( ChainOfFibers→FiberSeq F 2)
               ( puppe (ChainOfFibers→FiberSeq F 1))
               ( ProjOfFiberFiberSeq (fst , snd (ChainOfFibersEdges F 2))
             ∙ ( InclOfFiberFiberSeq (FiberSeqIncl F)) ⁻¹
             ∙ ( puppeProjEqFibIncl (ChainOfFibers→FiberSeq F 1)) ⁻¹)))
LoopSpacesInChainOfFibers F (suc (suc n)) =
  fst (PathPΣ (FibsEqOfFibSeq
               ( ChainOfFibers→FiberSeq F (3 + n))
               ( puppe (ChainOfFibers→FiberSeq F (2 + n)))
               ( ProjOfFiberFiberSeq
                 ( fst , snd (ChainOfFibersEdges F (suc (suc (suc n)))))
             ∙ ( InclOfFiberFiberSeq (ChainOfFibersEdges F (suc (suc n)))) ⁻¹
             ∙ ( puppeProjEqFibIncl (ChainOfFibers→FiberSeq F (suc (suc n)))) ⁻¹)))

LoopSpacesInChainOfFibers' : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → (ChainOfFibersVertices F (n · 3) ≡ (Ω^ n) C)
   × (ChainOfFibersVertices F (suc (n · 3)) ≡ (Ω^ n) B)
   × (ChainOfFibersVertices F (suc (suc (n · 3))) ≡ (Ω^ n) A)
LoopSpacesInChainOfFibers' F zero = refl , refl , refl
LoopSpacesInChainOfFibers' F (suc n) =
  LoopSpacesInChainOfFibers F (n · 3)
  ∙ cong Ω (fst (LoopSpacesInChainOfFibers' F n)) ,
  LoopSpacesInChainOfFibers F (suc (n · 3))
  ∙ cong Ω (fst (snd (LoopSpacesInChainOfFibers' F n))) ,
  LoopSpacesInChainOfFibers F (suc (suc (n · 3)))
  ∙ cong Ω (snd (snd (LoopSpacesInChainOfFibers' F n)))
