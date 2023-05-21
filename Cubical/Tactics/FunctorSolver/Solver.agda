{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Tactics.FunctorSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Id renaming (refl to reflId) hiding (_∙_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.Functor
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Functor renaming (Id to IdF)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Graph.Base

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open NatIso
open NatTrans

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  open FreeFunctor (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  
  Free𝓒 = FG
  η𝓒 = ηG
  Free𝓓 = FH
  η𝓓 = ηH
  Free𝓕 = Fϕ
  𝓟 = PowerCategory (Free𝓓 .ob) (SET (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd'))
  PsYo : Functor Free𝓓 𝓟
  PsYo = PseudoYoneda {C = Free𝓓}

  module TautoSem = Semantics {𝓒 = 𝓒} {𝓓 = 𝓓} {𝓕 = 𝓕} IdHom IdHom reflId
  module YoSem = Semantics {𝓒 = 𝓟} {𝓓 = 𝓟} {𝓕 = IdF}
                   (Uhom (PsYo ∘F Free𝓕) ∘GrHom η𝓒)
                   (Uhom           PsYo  ∘GrHom η𝓓)
                   reflId

  Yo-YoSem-Agree : Path _ PsYo YoSem.semH
  Yo-YoSem-Agree = sem-uniq-H where
    open YoSem.Uniqueness (PsYo ∘F Free𝓕) PsYo F-rUnit refl refl
           (compPath→Square (symPath (lUnit (idToPath reflId))
                            ∙ idToPathRefl
                            ∙ rUnit refl))
  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (p : Path _ (YoSem.semH ⟪ e ⟫) (YoSem.semH ⟪ e' ⟫))
        → Path _ (TautoSem.semH ⟪ e ⟫) (TautoSem.semH ⟪ e' ⟫)
  solve {A}{B} e e' p = congPath (TautoSem.semH .F-hom) (isFaithfulPseudoYoneda _ _ _ _ lem) where
    lem : Path _ (PsYo ⟪ e ⟫) (PsYo ⟪ e' ⟫)
    lem = transportPath (λ i → Path _ (Yo-YoSem-Agree (~ i) ⟪ e ⟫) (Yo-YoSem-Agree (~ i) ⟪ e' ⟫)) p

solve = Eval.solve
