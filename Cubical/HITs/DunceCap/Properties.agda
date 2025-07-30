
module Cubical.HITs.DunceCap.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.S1 using (S¹; base; decodeEncode)
import Cubical.HITs.S1 as S¹

open import Cubical.HITs.MappingCones
open import Cubical.HITs.DunceCap.Base

-- DunceCone is contractible (easy)

Disk : Type₀
Disk = Cone (idfun S¹)

isContr-Disk : isContr Disk
fst isContr-Disk = hub
snd isContr-Disk (inj x)     i = spoke x i
snd isContr-Disk hub         i = hub
snd isContr-Disk (spoke x j) i = spoke x (i ∧ j)

dunceMap≡id : dunceMap ≡ idfun S¹
dunceMap≡id i base = base
dunceMap≡id i (S¹.loop j) = p i j
  where p : S¹.loop ⁻¹ ∙∙ S¹.loop ∙∙ S¹.loop ≡ S¹.loop
        p = sym (decodeEncode base (S¹.loop ⁻¹ ∙∙ S¹.loop ∙∙ S¹.loop)) ∙ sym (lUnit S¹.loop)

isContr-DunceCone : isContr DunceCone
isContr-DunceCone = subst isContr (cong Cone (sym dunceMap≡id)) isContr-Disk

-- Dunce is contractible (harder)

contrDunce : (d : Dunce) → d ≡ base
contrDunce base k = loop k
contrDunce (loop i) k = surf k i
contrDunce (surf i j) k
  = hcomp (λ l → λ { (i = i0) → surf k j
                   ; (i = i1) → cube l
                   ; (j = i0) → cube l
                   ; (j = i1) → cube l
                   ; (k = i0) → surf i j
                   ; (k = i1) → base })
          (surf (k ∨ i) j)
  where cube : I → Dunce
        cube l = hfill (λ i → λ { (k = i0) → loop i
                                ; (k = i1) → base
                                ; (l = i0) → loop (k ∨ i)
                                ; (l = i1) → surf k i })
                       (inS (loop k)) i

isContr-Dunce : isContr Dunce
fst isContr-Dunce = base
snd isContr-Dunce = sym ∘ contrDunce


Dunce≡DunceCone : Dunce ≡ DunceCone
Dunce≡DunceCone = ua (isContr→Equiv isContr-Dunce isContr-DunceCone)
