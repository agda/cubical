{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.DunceCap.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.S1
open import Cubical.HITs.MappingCones

open import Cubical.HITs.DunceCap.Base

-- the dunce cap is contractible

Disk : Type₀
Disk = Cone (idfun S¹)

isContr-Disk : isContr Disk
fst isContr-Disk = hub
snd isContr-Disk (inj x)     i = spoke x i
snd isContr-Disk hub         i = hub
snd isContr-Disk (spoke x j) i = spoke x (i ∧ j)

dunceMap≡id : dunceMap ≡ idfun S¹
dunceMap≡id i base = base
dunceMap≡id i (loop j) = eq i j
  where eq : loop ⁻¹ ∙∙ loop ∙∙ loop ≡ loop
        eq = sym (decodeEncode base (loop ⁻¹ ∙∙ loop ∙∙ loop)) ∙ sym (lUnit loop)

isContr-Dunce : isContr Dunce
isContr-Dunce = subst isContr (cong Cone (sym dunceMap≡id)) isContr-Disk
