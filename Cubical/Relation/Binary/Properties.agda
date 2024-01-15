{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓA ℓA' ℓB ℓB' : Level
    A : Type ℓA
    B : Type ℓB
    f : A → B
    rA : Rel A A ℓA'
    rB : Rel B B ℓB'

open BinaryRelation

module _ (R : Rel B B ℓB') where

  -- Pulling back a relation along a function.
  -- This can for example be used when restricting an equivalence relation to a subset:
  --   _~'_ = on fst _~_

  pulledbackRel : (A → B) → Rel A A ℓB'
  pulledbackRel f x y = R (f x) (f y)

  funRel : Rel (A → B) (A → B) _
  funRel f g = ∀ x → R (f x) (g x)

module _ (isEquivRelR : isEquivRel rB) where
 open isEquivRel

 isEquivRelPulledbackRel : (f : A → _) → isEquivRel (pulledbackRel rB f)
 reflexive (isEquivRelPulledbackRel _) _ = reflexive isEquivRelR _
 symmetric (isEquivRelPulledbackRel _) _ _ = symmetric isEquivRelR _ _
 transitive (isEquivRelPulledbackRel _) _ _ _ = transitive isEquivRelR _ _ _

 isEquivRelFunRel : isEquivRel (funRel rB {A = A})
 reflexive isEquivRelFunRel _ _ =
   reflexive isEquivRelR _
 symmetric isEquivRelFunRel _ _ =
   symmetric isEquivRelR _ _ ∘_
 transitive isEquivRelFunRel _ _ _ u v _ =
   transitive isEquivRelR _ _ _ (u _) (v _)

module _ (rA : Rel A A ℓA') (rB : Rel B B ℓB') where

 ×Rel : Rel (A × B) (A × B) (ℓ-max ℓA' ℓB')
 ×Rel (a , b) (a' , b') = (rA a a') × (rB b b')

module _ (isEquivRelRA : isEquivRel rA) (isEquivRelRB : isEquivRel rB) where
 open isEquivRel

 private module eqrA = isEquivRel isEquivRelRA
 private module eqrB = isEquivRel isEquivRelRB

 isEquivRel×Rel : isEquivRel (×Rel rA rB)
 reflexive isEquivRel×Rel _ =
   eqrA.reflexive _ , eqrB.reflexive _
 symmetric isEquivRel×Rel _ _ =
   map-× (eqrA.symmetric _ _) (eqrB.symmetric _ _)
 transitive isEquivRel×Rel _ _ _ (ra , rb) =
   map-× (eqrA.transitive _ _ _ ra) (eqrB.transitive _ _ _ rb)


module _ (rA : Rel A A ℓA') (rB : Rel A A ℓB') where

 ⊓Rel : Rel A A (ℓ-max ℓA' ℓB')
 ⊓Rel a a' = (rA a a') × (rB a a')

module _ {rA : Rel A A ℓA} {rA' : Rel A A ℓA'}
  (isEquivRelRA : isEquivRel rA) (isEquivRelRA' : isEquivRel rA') where
 open isEquivRel

 private module eqrA = isEquivRel isEquivRelRA
 private module eqrA' = isEquivRel isEquivRelRA'

 isEquivRel⊓Rel : isEquivRel (⊓Rel rA rA')
 reflexive isEquivRel⊓Rel _ = eqrA.reflexive _ , eqrA'.reflexive _ 
 symmetric isEquivRel⊓Rel _ _ (r , r') =
  eqrA.symmetric _ _ r , eqrA'.symmetric _ _ r' 
 transitive isEquivRel⊓Rel _ _ _ (r , r') (q , q') =
    eqrA.transitive' r q , eqrA'.transitive' r' q' 

module _ {A B : Type ℓA} (e : A ≃ B) {_∼_ : Rel A A ℓA'} {_∻_ : Rel B B ℓA'}
         (_h_ : ∀ x y → (x ∼ y) ≃ ((fst e x) ∻ (fst e y))) where

  RelPathP : PathP (λ i → ua e i → ua e i → Type _)
              _∼_ _∻_
  RelPathP i x y = Glue  (ua-unglue e i x ∻ ua-unglue e i y)
      λ { (i = i0) → _ ,  x h y
        ; (i = i1) → _ , idEquiv _ }


module _ {ℓ''} {B : Type ℓB} {_∻_ : B → B → Type ℓB'} where

  JRelPathP-Goal : Type _
  JRelPathP-Goal = ∀ (A : Type ℓB) (e : A ≃ B) (_~_ : A → A → Type ℓB')
             → (_h_ :  ∀ x y → x ~ y ≃ (fst e x ∻ fst e  y)) → Type ℓ''


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
