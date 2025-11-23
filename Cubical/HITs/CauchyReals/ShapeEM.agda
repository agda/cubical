{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.ShapeEM where

open import Cubical.Foundations.Prelude renaming (Cube to PreludeCube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
-- open import Cubical.Data.Fin

import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Vec as V
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos;ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.CircleMore
open import Cubical.HITs.Sn as Sn
open import Cubical.HITs.S1 as S1
open import Cubical.HITs.Susp
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Categories.Category

-- open import Cubical.WildCat.Base

open import Cubical.Algebra.Group.ZAction

open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

import Cubical.Homotopy.Loopspace as Lsp
import Cubical.Homotopy.Group.Base as HG

open import Cubical.HITs.SequentialColimit as Seq
open import Cubical.Data.Sequence
import Cubical.Foundations.Pointed as P

open import Cubical.Foundations.Cubes

-- open import Cubical.Categories.Category renaming (isIso to isCIso)
-- open import Cubical.Categories.Monoidal
-- open import Cubical.Categories.Functor

-- open import Cubical.HITs.CauchyReals.BoundaryHIT

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.HITs.Truncation as T

import Cubical.HITs.EilenbergMacLane1 as EM₁

open import Cubical.HITs.TypeQuotients as TypeQuot using (_/ₜ_ ; [_] ; eq/)

private
  variable
   ℓ ℓ' ℓ'' : Level
   X : Type ℓ

-- open Category
-- open TensorStr

module _ {ℓ} (A : AbGroup ℓ) where

 module AG = AbGroupStr (snd A)
 open GroupTheory (AbGroup→Group A)

 data _gm∼_ : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ where
  [_∼+_] : ∀ a b → a gm∼ (a AG.+ b)

 make∼ : ∀ a a' → a gm∼ a'
 make∼ a a' =
  subst (a gm∼_) (AG.+Assoc _ _ _ ∙∙ cong (AG._+ a') (AG.+InvR _) ∙∙ AG.+IdL _)
   [ a ∼+ AG.- a AG.+ a' ]
 
 gmEqRel : BinaryRelation.isEquivRel _gm∼_
 gmEqRel .BinaryRelation.isEquivRel.reflexive a =
   subst (a gm∼_) (AG.+IdR _) [ a ∼+ AG.0g ]
 gmEqRel .BinaryRelation.isEquivRel.symmetric _ _ [ a ∼+ b ] =
  subst ((a AG.+ b) gm∼_) (sym (AG.+Assoc _ _ _)
   ∙∙ cong (a AG.+_) (AG.+InvR _) ∙∙ AG.+IdR _)
   [ (a AG.+ b) ∼+ AG.- b ]
 gmEqRel .BinaryRelation.isEquivRel.transitive _ _ _
   [ a ∼+ b ] [ .(a AG.+ b) ∼+ d ] =
  subst (a gm∼_) (AG.+Assoc a b d) [ a ∼+ b AG.+ d ]

 module GM∼ = BinaryRelation.isEquivRel gmEqRel

 GM : Type ℓ
 GM = ⟨ A ⟩ // GM∼.transitive

 GM∙ : P.Pointed ℓ
 GM∙ = GM , [ AG.0g ]//

 GM→∙EM₁ : GM∙ P.→∙ EM∙ A 1 
 GM→∙EM₁ .fst = GQ.rec
  GM∼.transitive
   EM₁.emsquash
   (λ _ → EM₁.embase)
   w ww --λ _ _ → {!EM₁.emcomp _ _!}
   where
   w : {a b : ⟨ A ⟩} → a gm∼ b → EM₁.embase ≡ EM₁.embase
   w [ a ∼+ b ] = EM₁.emloop b

   ww : {a b c : ⟨ A ⟩} (r : a gm∼ b) (s : b gm∼ c) →
      Square (w r) (w (GM∼.transitive a b c r s)) refl (w s)
   ww [ a ∼+ b ] [ .(a AG.+ b) ∼+ d ] =
     EM₁.emcomp _ _ ▷ (cong EM₁.emloop (sym (transportRefl _))
      ∙ sym (transportRefl _))
 GM→∙EM₁ .snd = refl

 IsoΩGM-EM : BijectionIso (HG.πGr 1 GM∙) (HG.πGr 1 (EM∙ A 1) )
 IsoΩGM-EM .BijectionIso.fun = HG.πHom 1 GM→∙EM₁ 
 IsoΩGM-EM .BijectionIso.inj =
  ST.elim (λ u → isProp→isSet (isPropΠ λ z →
    ST.squash₂
     u
     (GroupStr.1g (snd (HG.πGr 1 GM∙)))))
   λ u → 
     
     PT.elim (λ z → ST.squash₂ ∣ u ∣₂ ∣ refl ∣₂)
      (λ x → {!cong ∣_∣₂ ?!})
      ∘ Iso.fun PathIdTrunc₀Iso
     
 IsoΩGM-EM .BijectionIso.surj = {!!}



-- -- open BinaryRelation


-- -- spheres-path : ∀ (A : P.Pointed ℓ) n
-- --    → isOfHLevel (2 ℕ.+ n) (fst A)
-- --    → (f : S₊∙ (suc n) P.→∙ A) →
-- --     ∀ s → fst f s ≡ P.pt A
-- -- spheres-path A n hLevelA (f , f-pt) =
-- --   Sn.sphereElim n (λ _ → hLevelA _ _) f-pt


-- -- record GSeq (obj : ℕ → Type)
-- --             (_≋_ : ∀ {n} → Rel (obj n) (obj n) ℓ-zero) : Type₁ where
-- --  field
-- --   isEquivRel≋ : ∀ n → isEquivRel (_≋_ {n})
-- --   obj-inv : ∀ {n} → obj n → obj n
-- --   obj-inv-funct : ∀ {n} → (a a' : obj n) → a ≋ a' → obj-inv a ≋ obj-inv a'
-- --   _⊙_ : ∀ {n} → obj n → obj n → obj n
-- --   ⊙-sym : ∀ n → (a b : obj n) → (a ⊙ b) ≋ (b ⊙ a)
-- --   ⊙-funct : ∀ n → (a a' b : obj n) → a ≋ a' → (a ⊙ b) ≋ (a' ⊙ b)
-- --   unit : ∀ {n} → obj n
-- --   σIso : ∀ {n} → Iso (obj (suc n))
-- --     (Σ ((obj n) × (obj n)) λ (o , o') → (o ≋ o'))
-- --   σIso⊙ : ∀ {n} {a} {b} {c} x y →
-- --     (Iso.inv (σIso {n}) ((a , b) , x) ⊙ Iso.inv (σIso {n}) ((b , c) , y)) ≋
-- --      Iso.inv σIso (_ , isEquivRel.transitive (isEquivRel≋ n)
-- --       _ _ _ x y) 
  
-- --   -- middle-≋ : ∀ n (a b : obj (suc n)) → a ≋ b → fst (middle a) ≋ fst (middle b)
-- --   -- obj₋₁ : Type
-- --   -- obj₋₁-unit : obj₋₁
-- --   -- obj₀-ev : obj zero → S¹ → obj₋₁
-- --   -- obj₋₁-pt : (x : obj zero) → obj₋₁-ev x (ptSn 1) ≡ obj₋₁-unit


-- --  -- middle : ∀ {n} →  (obj (suc n)) → (Σ (obj n) λ m → (unit ≋ m) × (unit ≋ m))
-- --  -- middle {n} = Iso.fun (middleIso {n})


-- --  obj/ : ℕ → Type
-- --  obj/ n = (obj n / _≋_)


-- --  _⊙/_ : ∀ {n} → obj/ n → obj/ n → obj/ n
-- --  _⊙/_ {n} = setQuotSymmBinOp
-- --    (isEquivRel.reflexive (isEquivRel≋ n))
-- --    (isEquivRel.transitive (isEquivRel≋ n))
-- --    _⊙_ (⊙-sym n) (⊙-funct n)

-- --  _∙≋_ : ∀ {n} → {a b c : obj n} → a ≋ b → b ≋ c → a ≋ c
-- --  _∙≋_ {n} = isEquivRel.transitive (isEquivRel≋ n) _ _ _

-- --  -- split≋ : ∀ n → Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m)) →
-- --  --                 Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m)) → Type
-- --  -- split≋ n (o , (o₀ , o₁)) (o' , (o'₀ , o'₁)) =
-- --  --   Σ[ o≋o' ∈ (o ≋ o') ]
-- --  --      (split≋Half n o o' o≋o' o₀ o'₀)
-- --  --       × split≋Half n o o' o≋o' o₁ o'₁


-- --  field
   
-- --    isAbGrp⊙/ : ∀ n →
-- --      IsAbGroup [ unit {n} ]/ _⊙/_ (setQuotUnaryOp obj-inv obj-inv-funct)
   


-- --  isSetObj : ∀ n → isSet (obj n)
-- --  isSetObj = {!!}
-- --    -- reflOver≋ : ∀ n →
-- --    --   GQ.RelOver {ℓ''' = ℓ-zero}
-- --    --   (λ o → ((unit {n = n} ≋ o))) (_≋_ {n}) (isEquivRel≋ n)

-- --    -- to-middle-≋ : ∀ n
-- --    --   → {a b : Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m))} →
-- --    --    Iso.inv middleIso a ≋ Iso.inv middleIso b →
-- --    --    RelOver.RΣ (RelOver× (_≋_ unit) _≋_ (isEquivRel≋ n) (reflOver≋ n))
-- --    --    a b

-- --    -- from-middle-≋ : ∀ n {a b : Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m))} →
-- --    --    RelOver.RΣ (RelOver× (_≋_ unit) _≋_ (isEquivRel≋ n) (reflOver≋ n))
-- --    --    a b →
-- --    --    Iso.inv middleIso a ≋ Iso.inv middleIso b
   

-- --  module _ {n : ℕ} where
-- --   module ER≋ = isEquivRel (isEquivRel≋ n) 
 
-- --  -- middleIso/ : ∀ n → Iso (obj/ (suc n))
-- --  --     ∥ Σ (obj n // ER≋.transitive) _ ∥₂
-- --  -- middleIso/ n =
-- --  --   compIso
-- --  --     (liftIso/ _ middleIso )
-- --  --     (compIso
-- --  --       (relBiimpl→TruncIso
-- --  --         (to-middle-≋ n)
-- --  --         (from-middle-≋ n))
-- --  --       (RelOver.Σ/Iso (RelOver× _ _ _ (reflOver≋ n))))

-- --  -- obj-abGrpStr : ∀ n → AbGroupStr (obj n / _≋_)
-- --  -- obj-abGrpStr n = abgroupstr _ _ _ (isAbGrp⊙/ n)
 
-- --  -- objAbGroup : ℕ → AbGroup ℓ-zero 
-- --  -- objAbGroup n = _ , obj-abGrpStr n

-- --  GM-raw : ℕ → ℕ → Type
-- --  GM-raw n zero = obj n // ER≋.transitive
-- --  GM-raw n (suc k) =
-- --    hLevelTrunc (3 ℕ.+ k) (Susp (GM-raw n k))

-- --  merid-GM-sq : ∀ n a b → a ≋ b →
-- --    Square {A = Susp (GM-raw (suc n) zero)}
-- --     (merid [ a ]//)
-- --     (merid [ b ]//)
-- --     refl
-- --     refl
-- --  merid-GM-sq n a b r i i₁ =
-- --   merid (eq// r i) i₁

-- --  merid-GM-comp : ∀ n a b →
-- --    Square {A = Susp (GM-raw (suc n) zero)}
-- --     (merid [ a ⊙ b ]//)
-- --     (sym (merid [ unit ]//))
-- --     (merid [ a ]//)
-- --     (sym (merid [ b ]//))
-- --  merid-GM-comp n a b =
-- --   {!!}



-- --  shSequenceMap : ∀ n k
-- --    → GM-raw n k
-- --    → GM-raw (suc n) (suc k)
-- --  shSequenceMap n zero =
-- --   GQ.rec ER≋.transitive
-- --    (isOfHLevelTrunc 3)
-- --    (λ x → ∣ north ∣ₕ)
-- --    (λ {a} {b} a≋b →
-- --     cong ∣_∣ (merid [ Iso.inv σIso (_ , a≋b) ]// ∙ merid [ unit ]// ⁻¹))
-- --    λ {a} {b} {c} a≋b b≋c → congP (λ _ → cong ∣_∣)
-- --      (symP (compPathR→PathP∙∙
-- --        (cong (_∙ (merid [ unit ]// ⁻¹))
-- --               (sym (merid-GM-sq _ _ _ (σIso⊙ _  _))
-- --                ∙ 
-- --              (PathP→compPathR∙∙
-- --                (merid-GM-comp _ _ _)
-- --               ∙ doubleCompPath-elim
-- --                (merid [ Iso.inv σIso (_ , a≋b) ]//)
-- --                (merid [ unit ]// ⁻¹)
-- --                (merid [ Iso.inv σIso (_ , b≋c) ]//)))
-- --               ∙ sym (assoc _ _ _))))

-- -- -- (λ i →
-- -- --          (merid [ Iso.inv σIso ((a , c) , ER≋.transitive a b c r s) ]// ∙
-- -- --           merid [ unit ]// ⁻¹)
-- -- --          i)
-- -- --       ≡
-- -- --       ((λ i → north) ∙∙
-- -- --        (λ i →
-- -- --           (merid [ Iso.inv σIso ((a , b) , r) ]// ∙ merid [ unit ]// ⁻¹) i)
-- -- --        ∙∙
-- -- --        sym
-- -- --        (λ i →
-- -- --           (merid [ Iso.inv σIso ((b , c) , s) ]// ∙ merid [ unit ]// ⁻¹)
-- -- --           (~ i)))

-- --  shSequenceMap n (suc k) =
-- --    T.rec {!!} (∣_∣ₕ ∘ suspFun (shSequenceMap n k))
 
-- --  ShSequence : Sequence ℓ-zero
-- --  ShSequence .Sequence.obj n = GM-raw n n
-- --  ShSequence .Sequence.map {n} = shSequenceMap n n
 

-- -- -- GSeqSuc : ∀ (obj : ℕ → Type)
-- -- --             (_≋_ : ∀ {n} → Rel (obj n) (obj n) ℓ-zero)
-- -- --           → GSeq obj _≋_ → GSeq (obj ∘ suc) _≋_
-- -- -- GSeqSuc obj _≋_ gseq = w
-- -- --  where
-- -- --  module G = GSeq gseq
-- -- --  w : GSeq (obj ∘ suc) _≋_
-- -- --  w .GSeq.isEquivRel≋ n = G.isEquivRel≋ (suc n)
-- -- --  w .GSeq.obj-inv = G.obj-inv 
-- -- --  w .GSeq.obj-inv-funct = G.obj-inv-funct
-- -- --  w .GSeq._⊙_ = G._⊙_
-- -- --  w .GSeq.⊙-sym = G.⊙-sym ∘ suc
-- -- --  w .GSeq.⊙-funct = G.⊙-funct ∘ suc
-- -- --  w .GSeq.unit = G.unit
-- -- --  w .GSeq.middleIso = G.middleIso
-- -- --  w .GSeq.isAbGrp⊙/ = G.isAbGrp⊙/ ∘ suc
-- -- --  w .GSeq.reflOver≋ = G.reflOver≋ ∘ suc
-- -- --  w .GSeq.to-middle-≋ = G.to-middle-≋ ∘ suc
-- -- --  w .GSeq.from-middle-≋ = G.from-middle-≋ ∘ suc
