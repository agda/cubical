{-# OPTIONS --hidden-argument-puns #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
    R S : Rel A B ℓ''

record isIdentitySystem {A : Type ℓ} (a : A) (C : A → Type ℓ') (r : C a) : Type (ℓ-max ℓ ℓ') where
  field
    toPath : ∀ {b} → C b → a ≡ b
    toPathOver : ∀ {b} (p : C b) → PathP (λ i → C (toPath p i)) r p

  isContrTotal : ∃! A C
  isContrTotal = (a , r) , λ (b , p) → ΣPathP (toPath p , toPathOver p)

  -- Useful corollary
  toPathTotal-η : ΣPathP (toPath r , toPathOver r) ≡ refl
  toPathTotal-η = isContr→isSet isContrTotal _ _ _ _

  toPath-η : toPath r ≡ refl
  toPath-η = cong (cong fst) toPathTotal-η

  toPathOver-η : SquareP (λ i j → C (toPath-η i j)) (toPathOver r) refl refl refl
  toPathOver-η = cong (cong snd) toPathTotal-η

  IdsJ : ∀ {ℓ''} (P : ∀ b → C b → Type ℓ'') (Pr : P a r) {b} p → P b p
  IdsJ P Pr p = subst (uncurry P) (ΣPathP (toPath p , toPathOver p)) Pr

  IdsJ>_ : ∀ {ℓ''} {P : ∀ b → C b → Type ℓ''} (Pr : P a r) b p → P b p
  IdsJ>_ {P = P} Pr _ = IdsJ P Pr

  IdsJ-η : ∀ {ℓ''} (P : ∀ b → C b → Type ℓ'') (Pr : P a r) → IdsJ P Pr r ≡ Pr
  IdsJ-η P Pr i = transp (λ j → uncurry P (toPathTotal-η i j)) i Pr

  open Iso

  isoPath : ∀ b → Iso (C b) (a ≡ b)
  isoPath b .fun = toPath
  isoPath b .inv p = subst C p r
  isoPath b .rightInv p i j = hcomp (λ k → λ where
      (i = i0) → toPath (transport-filler (cong C p) r k) j
      (i = i1) → p (j ∧ k)
      (j = i0) → a
      (j = i1) → p k
    ) (toPath-η i j)
  isoPath b .leftInv p = fromPathP (toPathOver p)

open isIdentitySystem

isContrTotal→isIdentitySystem : {C : A → Type ℓ} (contr : ∃! A C)
                              → isIdentitySystem (contr .fst .fst) C (contr .fst .snd)
isContrTotal→isIdentitySystem contr .toPath     p = cong fst $ contr .snd (_ , p)
isContrTotal→isIdentitySystem contr .toPathOver p = cong snd $ contr .snd (_ , p)

-- Theorem 7.2.2 in the HoTT Book
module _ (R : Rel A A ℓ') where
  open BinaryRelation R

  reflPropRelImpliesIdentity→isSet : isRefl
                                   → isPropValued
                                   → impliesIdentity
                                   → isSet A
  reflPropRelImpliesIdentity→isSet Rrefl Rprop R→≡ = Collapsible≡→isSet λ where
    x y .fst p → R→≡ (subst (R x) p (Rrefl x))
    x y .snd p q → cong R→≡ (Rprop _ _ _ _)

  reflPropRelImpliesIdentity→isUnivalent : isRefl
                                         → isPropValued
                                         → impliesIdentity
                                         → isUnivalent
  reflPropRelImpliesIdentity→isUnivalent Rrefl Rprop R→≡ x y =
    propBiimpl→Equiv (Rprop x y) (Aset x y) R→≡ (λ p → subst (R x) p (Rrefl x)) where

    Aset : isSet A
    Aset = reflPropRelImpliesIdentity→isSet Rrefl Rprop R→≡

open HeterogenousRelation

-- Functional relations are equivalent to functions
module _ (A : Type ℓ) (B : Type ℓ') where
  FunctionalRel : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  FunctionalRel = Σ[ R ∈ Rel A B ℓ' ] isFunctionalRel R

  open Iso

  FunctionalRelIsoFunction : Iso FunctionalRel (A → B)
  FunctionalRelIsoFunction .fun (R , Rfun) a = Rfun a .fst .fst
  FunctionalRelIsoFunction .inv f = graphRel f , graphRelIsFunctional f
  FunctionalRelIsoFunction .rightInv f = refl
  FunctionalRelIsoFunction .leftInv (R , Rfun) = Σ≡Prop isPropIsFunctional $ funExt₂ λ a →
    isoToPath ∘ invIso ∘ isoPath (isContrTotal→isIdentitySystem $ Rfun a)

  Function≃FunctionalRel : (A → B) ≃ FunctionalRel
  Function≃FunctionalRel = isoToEquiv (invIso FunctionalRelIsoFunction)

-- Functional relations are closed under composition
isFunctionalCompRel : {R : Rel A B ℓ} {S : Rel B C ℓ'} → isFunctionalRel R → isFunctionalRel S → isFunctionalRel (compRel R S)
isFunctionalCompRel {A} {B} {C} {R} {S} Rfun Sfun a = isOfHLevelRetractFromIso 0 isom contr where

  contr : ∃! C (S (Rfun a .fst .fst))
  contr = Sfun (Rfun a .fst .fst)

  open Iso

  isom : Iso (Σ C (compRel R S a)) (Σ C (S (Rfun a .fst .fst)))
  isom = Σ-cong-iso-snd λ where
    -- This is almost Σ-contractFstIso (Rfun a), but I also reassociate the Σ-type
    c .fun (b , ab , bc) → subst⁻ (invRel S c) (cong fst (Rfun a .snd (b , ab))) bc
    c .inv ac → Rfun a .fst .fst , Rfun a .fst .snd , ac
    c .rightInv ac i → transp (λ j → S (isContr→isSet (Rfun a) _ _ (Rfun a .snd (Rfun a .fst)) refl i (~ j) .fst) c) i ac
    c .leftInv (b , ab , bc) i → _ , Rfun a .snd (b , ab) i .snd , subst⁻-filler (invRel S c) (cong fst (Rfun a .snd (b , ab))) bc (~ i)

-- Cofunctional relations are also closed under composition
isCofunctionalCompRel : {R : Rel A B ℓ} {S : Rel B C ℓ'} → isCofunctionalRel R → isCofunctionalRel S → isCofunctionalRel (compRel R S)
isCofunctionalCompRel {A} {B} {C} {R} {S} Rfun Sfun c = isOfHLevelRetractFromIso 0 isom contr where

  contr : ∃! A (invRel R (Sfun c .fst .fst))
  contr = Rfun (Sfun c .fst .fst)

  open Iso

  isom : Iso (Σ A (invRel (compRel R S) c)) (Σ A (invRel R (Sfun c .fst .fst)))
  isom = Σ-cong-iso-snd λ where
    -- This is almost Σ-contractFstIso (Sfun c), but I also reassociate the Σ-type
    a .fun (b , ab , bc) → subst⁻ (R a) (cong fst (Sfun c .snd (b , bc))) ab
    a .inv ab → Sfun c .fst .fst , ab , Sfun c .fst .snd
    a .rightInv ab i → transp (λ j → R a (isContr→isSet (Sfun c) _ _ (Sfun c .snd (Sfun c .fst)) refl i (~ j) .fst)) i ab
    a .leftInv (b , ab , bc) i → _ , subst⁻-filler (R a) (cong fst (Sfun c .snd (b , bc))) ab (~ i) , Sfun c .snd (b , bc) i .snd

-- Pulling back a relation along a function.
-- This can for example be used when restricting an equivalence relation to a subset:
--   _~'_ = on fst _~_

module _
  (f : A → B)
  (R : Rel B B ℓ)
  where

  open BinaryRelation

  pulledbackRel : Rel A A ℓ
  pulledbackRel x y = R (f x) (f y)

  isReflPulledbackRel : isRefl R → isRefl pulledbackRel
  isReflPulledbackRel isReflR a = isReflR (f a)

  isSymPulledbackRel : isSym R → isSym pulledbackRel
  isSymPulledbackRel isSymR a a' = isSymR (f a) (f a')

  isTransPulledbackRel : isTrans R → isTrans pulledbackRel
  isTransPulledbackRel isTransR a a' a'' = isTransR (f a) (f a') (f a'')

  open isEquivRel

  isEquivRelPulledbackRel : isEquivRel R → isEquivRel pulledbackRel
  reflexive (isEquivRelPulledbackRel isEquivRelR) = isReflPulledbackRel (reflexive isEquivRelR)
  symmetric (isEquivRelPulledbackRel isEquivRelR) = isSymPulledbackRel (symmetric isEquivRelR)
  transitive (isEquivRelPulledbackRel isEquivRelR) = isTransPulledbackRel (transitive isEquivRelR)

module _ {A B : Type ℓ} (e : A ≃ B) {_∼_ : Rel A A ℓ'} {_∻_ : Rel B B ℓ'}
         (_h_ : ∀ x y → (x ∼ y) ≃ ((fst e x) ∻ (fst e y))) where

  RelPathP : PathP (λ i → ua e i → ua e i → Type _)
              _∼_ _∻_
  RelPathP i x y = Glue (ua-unglue e i x ∻ ua-unglue e i y)
      λ { (i = i0) → _ , x h y
        ; (i = i1) → _ , idEquiv _ }


module _ {ℓ''} {B : Type ℓ} {_∻_ : B → B → Type ℓ'} where

  JRelPathP-Goal : Type _
  JRelPathP-Goal = ∀ (A : Type ℓ) (e : A ≃ B) (_~_ : A → A → Type ℓ')
             → (_h_ :  ∀ x y → x ~ y ≃ (fst e x ∻ fst e y)) → Type ℓ''


  EquivJRel : (Goal : JRelPathP-Goal)
            → (Goal _ (idEquiv _) _∻_ λ _ _ → idEquiv _ )
            → ∀ {A} e _~_ _h_ → Goal A e _~_ _h_
  EquivJRel Goal g {A} = EquivJ (λ A e → ∀ _~_ _h_ → Goal A e _~_ _h_)
   λ _~_ _h_ → subst (uncurry (Goal B (idEquiv B)))
       ((isPropRetract
           (map-snd (λ r → funExt₂ λ x y → sym (ua (r x y))))
           (map-snd (λ r x y → pathToEquiv λ i → r (~ i) x y))
           (λ (o , r) → cong (o ,_) (funExt₂ λ x y → equivEq
              (funExt λ _ → transportRefl _)))
          (isPropSingl {a = _∻_})) _ _) g
