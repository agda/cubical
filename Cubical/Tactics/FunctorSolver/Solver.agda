{-# OPTIONS --lossy-unification #-}
module Cubical.Tactics.FunctorSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Data.Graph.Base
open import Cubical.Data.Equality renaming (refl to reflEq)
  hiding (_∙_; sym; transport)

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Free.Functor
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Functor renaming (Id to IdF)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.UnderlyingGraph

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open NatIso
open NatTrans

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  open FreeFunctor (Cat→Graph 𝓒) (Cat→Graph 𝓓) (𝓕 .F-ob)

  Free𝓒 = FG
  η𝓒 = ηG
  Free𝓓 = FH
  η𝓓 = ηH
  Free𝓕 = Fϕ
  𝓟 = PowerCategory (Free𝓓 .ob) (SET (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd'))
  PsYo : Functor Free𝓓 𝓟
  PsYo = PseudoYoneda {C = Free𝓓}

  module TautoSem = Semantics {𝓒 = 𝓒} {𝓓 = 𝓓} {𝓕 = 𝓕} IdHom IdHom reflEq
  module YoSem = Semantics {𝓒 = 𝓟} {𝓓 = 𝓟} {𝓕 = IdF}
                   (Functor→GraphHom (PsYo ∘F Free𝓕) ∘GrHom η𝓒)
                   (Functor→GraphHom           PsYo  ∘GrHom η𝓓)
                   reflEq

  Yo-YoSem-Agree : Path _ PsYo YoSem.semH
  Yo-YoSem-Agree = sem-uniq-H where
    open YoSem.Uniqueness (PsYo ∘F Free𝓕) PsYo F-rUnit refl refl
           (compPath→Square (sym (lUnit (eqToPath reflEq))
                            ∙ rUnit refl))
  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (p : Path _ (YoSem.semH ⟪ e ⟫) (YoSem.semH ⟪ e' ⟫))
        → Path _ (TautoSem.semH ⟪ e ⟫) (TautoSem.semH ⟪ e' ⟫)
  solve {A}{B} e e' p =
    cong (TautoSem.semH .F-hom) (isFaithfulPseudoYoneda {C = Free𝓓} _ _ _ _ lem) where
    lem : Path _ (PsYo ⟪ e ⟫) (PsYo ⟪ e' ⟫)
    lem = transport
          (λ i → Path _
                      (Yo-YoSem-Agree (~ i) ⟪ e ⟫)
                      (Yo-YoSem-Agree (~ i) ⟪ e' ⟫))
          p

solve = Eval.solve
