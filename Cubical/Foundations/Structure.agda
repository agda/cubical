{-

In this directory we apply the cubical machinery to Martin Hötzel-Escardó's
structure identity principle:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Structure where

open import Cubical.Foundations.Structure.Base public
open import Cubical.Foundations.Structure.SNS public
open import Cubical.Foundations.Structure.SIP public

open import Cubical.Foundations.Structure.AddToStructure public
open import Cubical.Foundations.Structure.Pointed public
open import Cubical.Foundations.Structure.InftyMagma public
open import Cubical.Foundations.Structure.Monoid public
