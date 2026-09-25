{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.FiberOrCofiberSequences.LongExactSequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.ChainOfFibers
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.ShortExactSequence
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.ShortExact

private
  variable
    ℓ : Level

Ω^nHomotopyGroup≡ : (X : Pointed ℓ) (n m : ℕ)
  → πGr m ((Ω^ n) X) ≡ πGr (n + m) X
Ω^nHomotopyGroup≡ X 0 m = refl
Ω^nHomotopyGroup≡ X (suc n) m =
  uaGroup (GroupIso→GroupEquiv (GrIso-πΩ-π m))
  ∙ Ω^nHomotopyGroup≡ X n (suc m)
  ∙ cong (λ x → πGr x X) (+-suc n m)

Group≡→AbGroup≡ : (G H : AbGroup ℓ) → (AbGroup→Group G) ≡ (AbGroup→Group H)
  → G ≡ H
Group≡→AbGroup≡ G H p =
  equivFun (AbGroupPath G H) (transport (λ i → GroupEquiv (AbGroup→Group G) (p i)) idGroupEquiv)

AbGroup≡→Group≡ : (G H : Group ℓ)
  (cG : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y ≡ GroupStr._·_ (snd G) y x)
  (cH : (x y : ⟨ H ⟩) → GroupStr._·_ (snd H) x y ≡ GroupStr._·_ (snd H) y x)
  → Group→AbGroup G cG ≡ Group→AbGroup H cH
  → G ≡ H
AbGroup≡→Group≡ G H cG cH p = cong (AbGroup→Group) p

isLES : (V : ℕ → Group ℓ) → ((n : ℕ) → GroupHom (V (suc n)) (V n)) → Type ℓ
isLES V E =
  (n : ℕ) (x : ⟨ V (suc n) ⟩)
  → (isInIm (E (suc n)) x → isInKer (E n) x)
  × (isInKer (E n) x → isInIm (E (suc n)) x)

LES→isEquiv : (V : ℕ → Group ℓ) (E : (n : ℕ) → GroupHom (V (suc n)) (V n))
  (L : isLES V E) (n : ℕ) → V n ≡ UnitGroup
  → V (suc (suc (suc n))) ≡ UnitGroup → isEquiv (fst (E (suc n)))
LES→isEquiv V E L n VnUn V3+nUn =
  SES→isEquiv' (V3+nUn ⁻¹) (VnUn ⁻¹) (E (suc (suc n))) (E (suc n)) (E n)
  (λ x → snd (L (suc n) x)) λ x → snd (L n x)

LES→Equiv : (V : ℕ → Group ℓ) (E : (n : ℕ)
          → GroupHom (V (suc n)) (V n)) (L : isLES V E) (n : ℕ)
          → V n ≡ UnitGroup → V (suc (suc (suc n))) ≡ UnitGroup
          → GroupEquiv (V (suc (suc n))) (V (suc n))
fst (fst (LES→Equiv V E L n VnUn V3+nUn)) = fst (E (suc n))
snd (fst (LES→Equiv V E L n VnUn V3+nUn)) = LES→isEquiv V E L n VnUn V3+nUn
snd (LES→Equiv V E L n VnUn V3+nUn) = snd (E (suc n))

fiberSequence : {A B C : Pointed ℓ} → FiberSeq A B C → ℕ → Group ℓ
fiberSequence F n = πGr 0 (ChainOfFibersVertices F n)

fiberSequenceEdges : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → GroupHom (fiberSequence F (suc n)) (fiberSequence F n)
fiberSequenceEdges F n = πHom 0 (ChainOfFibersEdges F n)

fiberSequenceIsLES : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → isLES (fiberSequence F) (fiberSequenceEdges F)
fiberSequenceIsLES F n x =
  transport
   (λ i → (isInIm (πHom 0 (ChainOfFibers→FiberSeqIncl F n i)) x →
            isInKer (πHom 0 (ChainOfFibers→FiberSeqProj F n i)) x)
         × (isInKer (πHom 0 (ChainOfFibers→FiberSeqProj F n i)) x →
            isInIm (πHom 0 (ChainOfFibers→FiberSeqIncl F n i)) x))
   (FiberSeq→Exact (ChainOfFibers→FiberSeq F n) x)

fiberSequenceAbGroups : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ) →
  (x y : ⟨ fiberSequence F (suc (suc (suc n))) ⟩)
  → GroupStr._·_ (snd (fiberSequence F (suc (suc (suc n))))) x y
  ≡ GroupStr._·_ (snd (fiberSequence F (suc (suc (suc n))))) y x
fiberSequenceAbGroups F n =
  transport
  (λ i → (x y : ⟨ πGr 0 (LoopSpacesInChainOfFibers F n (~ i)) ⟩)
  → GroupStr._·_ (snd (πGr 0 (LoopSpacesInChainOfFibers F n (~ i)))) x y
  ≡ GroupStr._·_ (snd (πGr 0 (LoopSpacesInChainOfFibers F n (~ i)))) y x)
  (GroupEquivJ
  ( λ H e → (x y : ⟨ H ⟩) →
    GroupStr._·_ (snd H) x y ≡ GroupStr._·_ (snd H) y x)
  ( πGr-comm 0 (ChainOfFibersVertices F n))
  ( invGroupEquiv (GroupIso→GroupEquiv (GrIso-πΩ-π 0))))

FirstTermOfFiberSequence : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (fiberSequence F) 0 ≡ πGr 0 C
FirstTermOfFiberSequence F = refl

4SequenceOfFiberSequence : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → ((fiberSequence F) (n · 3) ≡ πGr n C)
  × ((fiberSequence F) (suc (n · 3)) ≡ πGr n B)
  × ((fiberSequence F) (suc (suc (n · 3))) ≡ πGr n A)
4SequenceOfFiberSequence {A = A} {B = B} {C = C} F zero =
  refl , refl , refl
4SequenceOfFiberSequence {A = A} {B = B} {C = C} F (suc n) =
  (cong (πGr 0) (fst (LoopSpacesInChainOfFibers' F (suc n)))
   ∙ Ω^nHomotopyGroup≡ C (suc n) 0
   ∙ cong (λ x → πGr (suc x) C) (+-zero n)) ,
  cong (πGr 0) (fst (snd (LoopSpacesInChainOfFibers' F (suc n))))
  ∙ Ω^nHomotopyGroup≡ B (suc n) 0
  ∙ cong (λ x → πGr (suc x) B) (+-zero n) ,
  cong (πGr 0) (snd (snd (LoopSpacesInChainOfFibers' F (suc n))))
  ∙ Ω^nHomotopyGroup≡ A (suc n) 0
  ∙ cong (λ x → πGr (suc x) A) (+-zero n)

4SequenceOfFiberSequenceAb : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → (Group→AbGroup ((fiberSequence F) ((suc n) · 3))
                     (fiberSequenceAbGroups F (n · 3)) ≡ πAb n C)
   × (Group→AbGroup ((fiberSequence F) (suc ((suc n) · 3)))
                     (fiberSequenceAbGroups F (suc (n · 3))) ≡ πAb n B)
   × (Group→AbGroup ((fiberSequence F) (suc (suc ((suc n) · 3))))
                     (fiberSequenceAbGroups F (suc (suc (n · 3)))) ≡ πAb n A)
4SequenceOfFiberSequenceAb {A = A} {B = B} {C = C} F n =
  (Group≡→AbGroup≡
   ( Group→AbGroup ((fiberSequence F) ((suc n) · 3))
                     (fiberSequenceAbGroups F (n · 3))) (πAb n C)
   ( fst (4SequenceOfFiberSequence F (suc n)))) ,
  (Group≡→AbGroup≡
   ( Group→AbGroup ((fiberSequence F) (suc ((suc n) · 3)))
                    (fiberSequenceAbGroups F (suc (n · 3)))) (πAb n B)
   ( fst (snd (4SequenceOfFiberSequence F (suc n))))) ,
  (Group≡→AbGroup≡
   ( Group→AbGroup ((fiberSequence F) (suc (suc ((suc n) · 3))))
                    (fiberSequenceAbGroups F (suc (suc (n · 3))))) (πAb n A)
   ( snd (snd (4SequenceOfFiberSequence F (suc n)))))

invAbGroupEquiv : (G H : AbGroup ℓ) → AbGroupEquiv G H → AbGroupEquiv H G
invAbGroupEquiv G H (e , eHom) = invGroupEquiv (e , eHom)

ExactSequenceEquiv : (A B C : Pointed ℓ) (n : ℕ) → FiberSeq A B C
  → (AbGroupEquiv {ℓ} {ℓ} (πAb (suc n) C) UnitAbGroup)
  → (AbGroupEquiv {ℓ} {ℓ} (πAb n C) UnitAbGroup)
  → AbGroupEquiv (πAb n A) (πAb n B)
ExactSequenceEquiv A B C n F πn+1CIsUnit πnCIsUnit =
  transport
  (λ i → AbGroupEquiv
         ((snd (snd (4SequenceOfFiberSequenceAb F n))) i)
         ((fst (snd (4SequenceOfFiberSequenceAb F n))) i))
  ( ((fst (fiberSequenceEdges F _)) ,
  ( LES→isEquiv (fiberSequence F) (fiberSequenceEdges F) (fiberSequenceIsLES F)
    ((suc n) · 3)
    (AbGroup≡→Group≡ (fiberSequence F ((suc n) · 3)) UnitGroup
                      (fiberSequenceAbGroups F (n · 3)) (λ _ _ → refl)
                      (fst (4SequenceOfFiberSequenceAb F n)
                         ∙ equivFun (AbGroupPath _ _) πnCIsUnit))
    (AbGroup≡→Group≡ (fiberSequence F ((suc (suc n)) · 3)) UnitGroup
                      (fiberSequenceAbGroups F ((suc n) · 3)) (λ _ _ → refl)
                      (fst (4SequenceOfFiberSequenceAb F (suc n))
                         ∙ equivFun (AbGroupPath _ _) πn+1CIsUnit)))) ,
  ( snd (fiberSequenceEdges F _)))
