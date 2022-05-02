{-

This file contains the classic isomorphism theorems for groups (so far
only the first theorem)

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.IsomorphismTheorems where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients renaming (_/_ to _/s_ ; rec to recS ; elim to elimS)
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.GroupPath

private
  variable
    ℓ : Level

-- The first isomorphism theorem: im ϕ ≃ G / ker ϕ
module _ {G H : Group ℓ} (ϕ : GroupHom G H) where

  open isSubgroup
  open Iso
  open GroupTheory


  kerNormalSubgroup : NormalSubgroup G
  kerNormalSubgroup = kerSubgroup ϕ , isNormalKer ϕ

  private
    imϕ : Group ℓ
    imϕ = imGroup ϕ

  -- for completeness:
  imNormalSubgroup : ((x y : ⟨ H ⟩)
    → GroupStr._·_ (snd H) x y ≡ GroupStr._·_ (snd H) y x)
    → NormalSubgroup H
  imNormalSubgroup comm = imSubgroup ϕ , isNormalIm ϕ comm

  private
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)
    module imG = GroupStr (snd imϕ)
    module kerG = GroupStr (snd (G / kerNormalSubgroup))
    module ϕ = IsGroupHom (ϕ .snd)

  f1 : ⟨ imϕ ⟩ → ⟨ G / kerNormalSubgroup ⟩
  f1 (x , Hx) = rec→Set ( squash/)
                         (λ { (y , hy) → [ y ]})
                         (λ { (y , hy) (z , hz) → eq/ y z (rem y z hy hz) })
                         Hx
    where
    rem : (y z : ⟨ G ⟩) → ϕ .fst y ≡ x → ϕ .fst z ≡ x → ϕ .fst (y G.· G.inv z) ≡ H.1g
    rem y z hy hz =
      ϕ .fst (y G.· G.inv z)        ≡⟨ ϕ.pres· _ _ ⟩
      ϕ .fst y H.· ϕ .fst (G.inv z) ≡⟨ cong (ϕ .fst y H.·_) (ϕ.presinv _) ⟩
      ϕ .fst y H.· H.inv (ϕ .fst z) ≡⟨ (λ i → hy i H.· H.inv (hz i)) ⟩
      x H.· H.inv x                 ≡⟨ H.invr x ⟩
      H.1g                          ∎

  f2 : ⟨ G / kerNormalSubgroup ⟩ → ⟨ imϕ ⟩
  f2 = recS imG.is-set (λ y → ϕ .fst y , ∣ y , refl ∣)
                       (λ x y r → Σ≡Prop (λ _ → squash)
                       (rem x y r))
    where
    rem : (x y : ⟨ G ⟩) → ϕ .fst (x G.· G.inv y) ≡ H.1g → ϕ .fst x ≡ ϕ .fst y
    rem x y r =
      ϕ .fst x                                      ≡⟨ sym (H.rid _) ⟩
      ϕ .fst x H.· H.1g                             ≡⟨ cong (ϕ .fst x H.·_) (sym (H.invl _)) ⟩
      ϕ .fst x H.· H.inv (ϕ .fst y) H.· ϕ .fst y    ≡⟨ (λ i → ϕ .fst x H.· ϕ.presinv y (~ i) H.· ϕ .fst y) ⟩
      ϕ .fst x H.· ϕ .fst (G.inv y) H.· ϕ .fst y    ≡⟨ H.assoc _ _ _ ⟩
      (ϕ .fst x H.· ϕ .fst (G.inv y)) H.· ϕ .fst y  ≡⟨ cong (H._· _) (sym (ϕ.pres· _ _)) ⟩
      ϕ .fst (x G.· G.inv y) H.· ϕ .fst y           ≡⟨ cong (H._· ϕ .fst y) r ⟩
      H.1g H.· ϕ .fst y                             ≡⟨ H.lid _ ⟩
      ϕ .fst y ∎

  f12 : (x : ⟨ G / kerNormalSubgroup ⟩) → f1 (f2 x) ≡ x
  f12 = elimProp (λ _ → squash/ _ _) (λ _ → refl)

  f21 : (x : ⟨ imϕ ⟩) → f2 (f1 x) ≡ x
  f21 (x , hx) = elim {P = λ hx → f2 (f1 (x , hx)) ≡ (x , hx)}
                      (λ _ → imG.is-set _ _)
                      (λ {(x , hx) → Σ≡Prop (λ _ → squash) hx})
                      hx

  f1-isHom : (x y : ⟨ imϕ ⟩) → f1 (x imG.· y) ≡ f1 x kerG.· f1 y
  f1-isHom (x , hx) (y , hy) =
    elim2 {P = λ hx hy → f1 ((x , hx) imG.· (y , hy)) ≡ f1 (x , hx) kerG.· f1 (y , hy)}
          (λ _ _ → kerG.is-set _ _) (λ _ _ → refl) hx hy

  -- The first isomorphism theorem for groups
  isoThm1 : GroupIso imϕ (G / kerNormalSubgroup)
  fun (fst isoThm1) = f1
  inv (fst isoThm1) = f2
  rightInv (fst isoThm1) = f12
  leftInv (fst isoThm1) = f21
  snd isoThm1 = makeIsGroupHom f1-isHom

  -- The SIP lets us turn the isomorphism theorem into a path
  pathThm1 : imϕ ≡ G / kerNormalSubgroup
  pathThm1 = uaGroup (GroupIso→GroupEquiv isoThm1)

  surjImIso : isSurjective ϕ → GroupIso imϕ H
  surjImIso surj =
    BijectionIso→GroupIso
      (bijIso indHom
              (uncurry
                (λ h → elim (λ _ → isPropΠ (λ _ → imG.is-set _ _))
                  (uncurry λ g y
                    → λ inker → Σ≡Prop (λ _ → squash) inker)))
              λ b → map (λ x → (b , ∣ x ∣) , refl) (surj b))
    where
    indHom : GroupHom imϕ H
    fst indHom = fst
    snd indHom = makeIsGroupHom λ _ _ → refl
