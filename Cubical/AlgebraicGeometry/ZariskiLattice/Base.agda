{-# OPTIONS --lossy-unification #-}
module Cubical.AlgebraicGeometry.ZariskiLattice.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈p_; _⊆_ to _⊆p_; subst-∈ to subst-∈p)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset
open import Cubical.Relation.Binary.Order.Poset.Instances.PosetalReflection as PR
open import Cubical.Functions.Embedding

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Matrix

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Tactics.CommRingSolver

open Iso
open BinaryRelation
open isEquivRel

private variable
  ℓ ℓ' : Level


module ZarLat (R' : CommRing ℓ) where
  open CommRingStr (snd R')
  open RingTheory (CommRing→Ring R')
  open Sum (CommRing→Ring R')
  open CommRingTheory R'
  open Exponentiation R'
  open BinomialThm R'
  open CommIdeal R'
  open RadicalIdeal R'
  open isCommIdeal
  open ProdFin R'
  open IdealSum R'

  private
    R = fst R'
    A = Σ[ n ∈ ℕ ] (FinVec R n)
    ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
    ⟨ V ⟩ = ⟨ V ⟩[ R' ]

  -- This is small!
  _≼_ : A → A → Type ℓ
  (_ , α) ≼ (_ , β) = √ ⟨ α ⟩ ⊆ √ ⟨ β ⟩

  isRefl≼ : ∀ {a} → a ≼ a
  isRefl≼ = ⊆-refl _

  isTrans≼ : ∀ {a b c : A} → a ≼ b → b ≼ c → a ≼ c
  isTrans≼ = ⊆-trans _ _ _

  ≼PropValued : isPropValued _≼_
  ≼PropValued x y = ⊆-isProp _ _

  isProset≼ : IsProset _≼_
  isProset≼ = isproset (isSetΣ isSetℕ λ x → isSet→ is-set) ≼PropValued (λ _ → isRefl≼) (λ _ _ _ → isTrans≼)

  _∼_ : A → A → Type ℓ -- \sim
  _∼_ = SymKernel _≼_

  ∼PropValued : isPropValued (_∼_)
  ∼PropValued _ _ = isProp× (≼PropValued _ _) (≼PropValued _ _)

  ∼EquivRel : isEquivRel (_∼_)
  ∼EquivRel = isProset→isEquivRelSymKernel isProset≼

  private
    AProset : Proset ℓ ℓ
    AProset = _ , prosetstr _≼_ isProset≼

  -- lives in the same universe as R
  ZLPoset : Poset ℓ ℓ
  ZLPoset = ReflectionPoset AProset

  ZL : Type ℓ
  ZL = ZLPoset .fst

  _≤ZL_ = ZLPoset .snd .PosetStr._≤_
  isPosetZL = ZLPoset .snd .PosetStr.isPoset
  isProsetZL = isPoset→isProset isPosetZL

  0a : A
  0a = 0 , λ ()

  1a : A
  1a = 1 , λ _ → 1r

  --  need something big in our proofs though:

  _∼≡_ : A → A → Type (ℓ-suc ℓ)
  (_ , α) ∼≡ (_ , β) = √ ⟨ α ⟩ ≡ √ ⟨ β ⟩

  ≡→∼ : ∀ {a b : A} → a ∼≡ b → a ∼ b
  ≡→∼ r = ⊆-refl-consequence _ _ (cong fst r)

  ∼→≡ : ∀ {a b : A} → a ∼ b → a ∼≡ b
  ∼→≡ r = CommIdeal≡Char (r .fst) (r .snd)

  ∼≃≡ : ∀ {a b : A} → (a ∼ b) ≃ (a ∼≡ b)
  ∼≃≡ = propBiimpl→Equiv (∼PropValued _ _) (isSetCommIdeal _ _) ∼→≡ ≡→∼

  0z : ZL
  0z = [ 0a ]

  0z-least : isLeast isProsetZL (_ , id↪ _) 0z
  0z-least = []presLeast AProset 0a λ x → √FGIdealCharRImpl _ _ λ ()

  1z : ZL
  1z = [ 1a ]

  1z-greatest : isGreatest isProsetZL (_ , id↪ _) 1z
  1z-greatest = []presGreatest AProset 1a λ x → √FGIdealCharRImpl _ _ λ _ →
    ∣ 0 , ∣ (λ _ → 1r) , solve! R' ∣₁ ∣₁

  _∨a_ : A → A → A
  (_ , α) ∨a (_ , β) = _ , α ++Fin β

  ∨a-join : ∀ x y → isJoin isProset≼ x y (x ∨a y)
  ∨a-join (_ , α) (_ , β) (_ , γ) = propBiimpl→Equiv (≼PropValued _ _) (isProp× (≼PropValued _ _) (≼PropValued _ _)) to fo
    where
      to : _
      to α∨β⊆γ .fst = ⊆-trans _ _ _
        (√Resp⊆ ⟨ α ⟩ ⟨ α ++Fin β ⟩ (⊆-trans _ _ _ (+iLincl ⟨ α ⟩ ⟨ β ⟩) (FGIdealAddLemmaRIncl _ α β))) α∨β⊆γ
      to α∨β⊆γ .snd = ⊆-trans _ _ _
        (√Resp⊆ ⟨ β ⟩ ⟨ α ++Fin β ⟩ (⊆-trans _ _ _ (+iRincl ⟨ α ⟩ ⟨ β ⟩) (FGIdealAddLemmaRIncl _ α β))) α∨β⊆γ
      fo : _
      fo (α⊆γ , β⊆γ) = ⊆-trans _ _ _ (√Resp⊆ ⟨ α ++Fin β ⟩ (⟨ α ⟩ +i ⟨ β ⟩) $ FGIdealAddLemmaLIncl _ α β) λ x x∈√α+β → do
        (n , x^n∈α+β) ← x∈√α+β
        ((y , z) , y∈α , z∈β , x^n≡y+z) ← x^n∈α+β
        ^∈√→∈√ _ x n $ subst-∈ (√ ⟨ γ ⟩) (sym x^n≡y+z) $
          √ ⟨ γ ⟩ .snd .+Closed (α⊆γ y (∈→∈√ _ y y∈α)) (β⊆γ z (∈→∈√ _ z z∈β))

  ZL-joins : isJoinSemipseudolattice ZLPoset
  ZL-joins = hasBinJoins AProset λ x y → _ , ∨a-join x y

  _∨z_ : ZL → ZL → ZL
  x ∨z y = ZL-joins x y .fst

  _∧a_ : A → A → A
  (_ , α) ∧a (_ , β) = _ , α ··Fin β

  ∧a-meet : ∀ x y → isMeet isProset≼ x y (x ∧a y)
  ∧a-meet (_ , α) (_ , β) (_ , γ) = propBiimpl→Equiv (≼PropValued _ _) (isProp× (≼PropValued _ _) (≼PropValued _ _)) to fo
    where
      to : _
      to γ≼α∧β .fst = ⊆-trans _ _ _ γ≼α∧β $ √Resp⊆ ⟨ α ··Fin β ⟩ ⟨ α ⟩ $
                      ⊆-trans _ _ _ (FGIdealMultLemmaLIncl _ α β) (·iLincl ⟨ α ⟩ ⟨ β ⟩)
      to γ≼α∧β .snd = ⊆-trans _ _ _ γ≼α∧β $ √Resp⊆ ⟨ α ··Fin β ⟩ ⟨ β ⟩ $
                      ⊆-trans _ _ _ (FGIdealMultLemmaLIncl _ α β) (·iRincl ⟨ α ⟩ ⟨ β ⟩)
      fo : _
      fo (γ≼α , γ≼β) = ⊆-trans _ _ _ (λ x x∈√γ →
          ∣ 2 , subst-∈ (√ ⟨ α ⟩ ·i √ ⟨ β ⟩) (solve! R') (prodInProd _ _ x x (γ≼α x x∈√γ) (γ≼β x x∈√γ)) ∣₁
        ) $ ⊆-trans _ _ _ (√·ContrLIncl ⟨ α ⟩ ⟨ β ⟩) $
        √Resp⊆ (⟨ α ⟩ ·i ⟨ β ⟩) ⟨ α ··Fin β ⟩ $ FGIdealMultLemmaRIncl _ α β

  ZL-meets : isMeetSemipseudolattice ZLPoset
  ZL-meets = hasBinMeets AProset λ x y → _ , ∧a-meet x y

  _∧z_ : ZL → ZL → ZL
  x ∧z y = ZL-meets x y .fst

  -- join axioms
  ∨zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∨z (𝔟 ∨z 𝔠) ≡ (𝔞 ∨z 𝔟) ∨z 𝔠
  ∨zAssoc = joinAssoc isPosetZL ZL-joins

  ∨zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∨z 𝔟 ≡ 𝔟 ∨z 𝔞
  ∨zComm = joinComm isPosetZL ZL-joins

  ∨zLid : ∀ (𝔞 : ZL) → 0z ∨z 𝔞 ≡ 𝔞
  ∨zLid = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

  ∨zRid : ∀ (𝔞 : ZL) → 𝔞 ∨z 0z ≡ 𝔞
  ∨zRid _ = ∨zComm _ _ ∙ ∨zLid _

  -- -- meet axioms
  ∧zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∧z 𝔠) ≡ (𝔞 ∧z 𝔟) ∧z 𝔠
  ∧zAssoc = meetAssoc isPosetZL ZL-meets

  ∧zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z 𝔟 ≡ 𝔟 ∧z 𝔞
  ∧zComm = meetComm isPosetZL ZL-meets

  ∧zRid : ∀ (𝔞 : ZL) → 𝔞 ∧z 1z ≡ 𝔞
  ∧zRid = SQ.elimProp (λ _ → squash/ _ _) λ (_ , α) → eq/ _ _ $ ≡→∼ $ cong √ $
    ⟨ α ··Fin (replicateFinVec 1 1r) ⟩ ≡⟨ FGIdealMultLemma _ _ _ ⟩
    ⟨ α ⟩ ·i ⟨ (replicateFinVec 1 1r) ⟩ ≡⟨ cong (⟨ α ⟩ ·i_) (contains1Is1 _ (indInIdeal _ _ zero)) ⟩
    ⟨ α ⟩ ·i 1Ideal                     ≡⟨ ·iRid _ ⟩
    ⟨ α ⟩ ∎

  -- absorption and distributivity
  ∧zAbsorb∨z : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z (𝔞 ∨z 𝔟) ≡ 𝔞
  ∧zAbsorb∨z = MeetAbsorbLJoin ZLPoset (ZL-meets , ZL-joins)

  ∧zLDist∨z : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∨z 𝔠) ≡ (𝔞 ∧z 𝔟) ∨z (𝔞 ∧z 𝔠)
  ∧zLDist∨z = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
    λ (_ , α) (_ , β) (_ , γ) → eq/ _ _ (≡→∼
      (√ ⟨ α ··Fin (β ++Fin γ) ⟩            ≡⟨ cong √ (FGIdealMultLemma _ _ _) ⟩
        √ (⟨ α ⟩ ·i ⟨ β ++Fin γ ⟩)           ≡⟨ cong (λ x → √ (⟨ α ⟩ ·i x)) (FGIdealAddLemma _ _ _) ⟩
        √ (⟨ α ⟩ ·i (⟨ β ⟩ +i ⟨ γ ⟩))        ≡⟨ cong √ (·iRdist+i _ _ _) ⟩
        -- L/R-dist are swapped
        -- in Lattices vs Rings
        √ (⟨ α ⟩ ·i ⟨ β ⟩ +i ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong₂ (λ x y → √ (x +i y))
                                                      (sym (FGIdealMultLemma _ _ _))
                                                      (sym (FGIdealMultLemma _ _ _)) ⟩
        √ (⟨ α ··Fin β ⟩ +i ⟨ α ··Fin γ ⟩)   ≡⟨ cong √ (sym (FGIdealAddLemma _ _ _)) ⟩
        √ ⟨ (α ··Fin β) ++Fin (α ··Fin γ) ⟩  ∎))

  ZariskiLattice : DistLattice ℓ
  fst ZariskiLattice = ZL
  DistLatticeStr.0l (snd ZariskiLattice) = 0z
  DistLatticeStr.1l (snd ZariskiLattice) = 1z
  DistLatticeStr._∨l_ (snd ZariskiLattice) = _∨z_
  DistLatticeStr._∧l_ (snd ZariskiLattice) = _∧z_
  DistLatticeStr.isDistLattice (snd ZariskiLattice) =
    makeIsDistLattice∧lOver∨l squash/ ∨zAssoc ∨zRid ∨zComm
                                        ∧zAssoc ∧zRid ∧zComm ∧zAbsorb∨z ∧zLDist∨z
