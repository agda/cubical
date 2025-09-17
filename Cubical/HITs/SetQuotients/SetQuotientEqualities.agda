{-

Set quotients:

-}

{-# OPTIONS --safe #-}
{-# OPTIONS --cubical #-}

module Cubical.HITs.SetQuotients.SetQuotientEqualities where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Binary.Base
open BinaryRelation 
open import Cubical.HITs.SetQuotients.Base 
open import Cubical.HITs.SetQuotients.Properties hiding (rec)
open import Cubical.HITs.PropositionalTruncation 
open import Cubical.HITs.PropositionalTruncation.Monad

private 
  variable
    ℓ ℓ' : Level

-----------------------------------------------------

-- This file provides various lemmas showing equality between syntactically different set quotients,
-- plus related and supporting lemmas.

-- The usual Iso isomorphism is generalized to Iso/R, a similar concept, but one defined upto any
-- equivalence relation on the set A. We can call such a generalized isomorphism an "isomorphism/R".
-- It is an isomorphism when the relation R is cubical equality _≡_, and when the pull back g
-- (or inv/R) is 1-to-1, ie it has an inverse. 

-----------
-- An Isomorphism, but upto equivalence R instead of equality _≡_:
module _  {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ} (ER : isEquivRel R) where
  
  retract/R : (f : A → B) → (g : B → A) → Type ℓ
  retract/R f g = ∀ a → R (g (f a)) a  

record Iso/R  (A : Type ℓ) (B : Type ℓ') {R : A → A → Type ℓ} (ER : isEquivRel R) : Type (ℓ-max ℓ ℓ') where
  --no-eta-equality
  constructor iso/R
  field
    fun/R : A → B
    inv/R : B → A
    leftInv/R  : retract/R ER fun/R inv/R

open Iso/R

-- R has an dual:
R* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} → B → B → Type ℓ
R* {ℓ}{ℓ'}{A}{B}{R}{ER} {iso/r} b b' = R (iso/r .inv/R b) (iso/r .inv/R b')

section/R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} → Type (ℓ-max ℓ ℓ')
section/R {iso/r = iso/r} = ∀ b → R* {iso/r = iso/r} (iso/r .fun/R (iso/r .inv/R b)) b  

retract/R→section/R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} →
  section/R {iso/r = iso/r} 
retract/R→section/R {R = R} {equivRel reflexive symmetric transitive} {iso/r = iso/r} b = iso/r .leftInv/R (iso/r .inv/R b)

--------------
-- A 'natural' isomorphism/R when A ≡ B:
iso/R-A≡B : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} → (AB : A ≡ B) → Iso/R A B ER
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .fun/R = λ z → transport AB z
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .inv/R = λ z → transport (sym AB) z
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .leftInv/R a = step1 (iso/R-A≡B {ℓ} {A}{B}{R}{ER} AB .inv/R (iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB .fun/R a)) a help
  where
    help : transport (sym AB) (transport AB a) ≡ a
    help = transport⁻Transport AB a
    step1 : ∀ x y → x ≡ y → R x y
    step1 x y xy = subst (R x) xy (reflexive x) 

ER≡ : (A : Type ℓ) → isEquivRel ((_≡_) {ℓ = ℓ} {A})
ER≡ {ℓ} A = equivRel (λ a i → a) (λ a b x i → x (~ i)) λ a b c x y i → (x ∙ y) i

-- Some lemmas about Iso/R
R→R* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → {iso/r : Iso/R A B {R} ER}{a a' : A}
  → R a a' → R* {iso/r = iso/r} (iso/r .fun/R a) (iso/r .fun/R a')
R→R* {ℓ}{ℓ'}{A}{B}{R} {ER} {iso/r} raa' =
  ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R _)) _ (iso/r .inv/R (iso/r .fun/R _))
  (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R _)) _ _ (iso/r .leftInv/R _) raa')
  (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R _)) _ (iso/r .leftInv/R _))
                                       
-- By definition:
R*→R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → {iso/r : Iso/R A B {R} ER}{b b' : B} →
  R* {iso/r = iso/r} b b' → R (iso/r .inv/R b) (iso/r .inv/R b')
R*→R z = z

-- That Iso/R, an isomorphism/R, is a generalised Iso isomorphism, seen by setting the equivalence relation on A
-- to _≡_ and assuming that inv/R has an inverse inv/R⁻¹, ie it is 1-to-1:
iso/R→≡→Iso : {A : Type ℓ} {B : Type ℓ'} →
  (iso/r : Iso/R {ℓ}{ℓ'} A B {R = (_≡_) {ℓ}{A}} (ER≡ A)) → (inv/R⁻¹ : A → B) → (∀ b → inv/R⁻¹ (iso/r .inv/R b) ≡ b) → Iso A B 
iso/R→≡→Iso {ℓ}{ℓ'}{A}{B} iso/r@(iso/R fun/R₁ inv/R₁ leftInv/R₁) inv/R⁻¹ invertible = iso fun/R₁ inv/R₁ section' leftInv/R₁
  where
    sectionR : section/R {ℓ}{ℓ'}{A}{B}{_≡_}{ER≡ A}{iso/r}
    sectionR = retract/R→section/R {iso/r = iso/r}
    step1 : ∀ b → (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ (inv/R₁ b)
    step1 b = R*→R {iso/r = iso/r} (sectionR b)
    step2 : ∀ b → inv/R⁻¹ (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ inv/R⁻¹ (inv/R₁ b)
    step2 b = cong (λ u → inv/R⁻¹ u) (step1 b)
    step3 : ∀ b → inv/R⁻¹ (inv/R₁ b) ≡ b
    step3 b = invertible b
    step4 : ∀ b → inv/R⁻¹ (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ fun/R₁ (inv/R₁ b)
    step4 b = invertible (fun/R₁ (inv/R₁ b))
    section' : ∀ b → fun/R₁ (inv/R₁ b) ≡ b
    section' b = (sym (step4 b) ∙ step2 b) ∙ step3 b 

-- R* is an equivalence relation too:
isEquivRelR* : (A : Type ℓ) (B : Type ℓ') {R : A → A → Type ℓ} {ER : isEquivRel R} → (iso/r : Iso/R A B ER) → isEquivRel (R* {iso/r = iso/r})
isEquivRelR* A B {R} {ER} iso/r = equivRel
  (λ a → ER .isEquivRel.reflexive (iso/r .inv/R a))
  (λ a b → ER .isEquivRel.symmetric (iso/r .inv/R a) (iso/r .inv/R b))
  (λ a b c → ER .isEquivRel.transitive (iso/r .inv/R a) (iso/r .inv/R b) (iso/r .inv/R c))
 
-- There is an induced isomorphism with respect to R*:
iso/R→Iso/R* : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} →
  (iso/r : Iso/R A B {R} ER) →
           Iso/R B A {R = R* {iso/r = iso/r}} (isEquivRelR* A B iso/r)
iso/R→Iso/R* iso/r = iso/R (iso/r .inv/R) (iso/r .fun/R) (λ a → iso/r .leftInv/R (iso/r .inv/R a)) 

-- The propositionality of R implies the propositionality of R*:
isPropR→IsPropR* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → (iso/r : Iso/R {ℓ} A B {R} ER)
  → (∀ a a' → isProp (R a a')) → (∀ b b' → isProp ((R* {iso/r = iso/r}) b b')) 
isPropR→IsPropR* iso/r ispRxy x y = ispRxy (iso/r .inv/R x) (iso/r .inv/R y) 

-- Duality gives an equality when isProp (R a a'):   [Auto-generated proof!]
R≡R**Hlp : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} →
  (iso/r : Iso/R {ℓ} A B {R} ER) →
  (∀ a a' → isProp (R a a')) →
  let R** = R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} in
  (∀ a a' → R a a' ≡ R** a a')
R≡R**Hlp {ℓ}{A}{B}{R}{ER} iso/r ispRxy a a' = isoToPath (iso
  (λ z → ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a' (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a a' (iso/r .leftInv/R a) z)
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a')) a' (iso/r .leftInv/R a')))
  (λ x → ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a')) a'
     (ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a)) (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a)) a (iso/r .leftInv/R a))  x) (iso/r .leftInv/R a'))
  (λ b → ispRxy (iso/r .inv/R (iso/r .fun/R a)) (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a' (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a a' (iso/r .leftInv/R a)
     (ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a')) a'
     (ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a)) (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a)) a (iso/r .leftInv/R a)) b) (iso/r .leftInv/R a')))
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a')) a' (iso/r .leftInv/R a'))) b)
  (λ a₁ → ispRxy a a' (ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a')) a'
     (ER .isEquivRel.transitive a (iso/r .inv/R (iso/r .fun/R a)) (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a)) a (iso/r .leftInv/R a))
     (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a' (iso/r .inv/R (iso/r .fun/R a'))
     (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R a)) a a' (iso/r .leftInv/R a) a₁)
     (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R a')) a' (iso/r .leftInv/R a')))) (iso/r .leftInv/R a')) a₁)) 

-- The isProp-duality lemma:
R≡R** : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} →
  (iso/r : Iso/R {ℓ} A B {R} ER) →
  (∀ a a' → isProp (R a a')) →
  let R** = (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r}) in
  R ≡ R**
R≡R** {ℓ}{A}{B}{R}{ER} iso/r ispRxy = funExt (λ a → funExt (λ a' → R≡R**Hlp iso/r ispRxy a a'))

-- Example of duality: 
isPropR→IsPropR** : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} → (iso/r : Iso/R {ℓ} A B {R} ER)
  → (∀ x y → isProp (R x y)) → (∀ x y → isProp (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y)) 
isPropR→IsPropR** {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} iso/r x y ispRxy = λ x' y'
  → x (iso/r .inv/R (iso/r .fun/R y)) (iso/r .inv/R (iso/r .fun/R ispRxy)) x' y'

-- Same isProp-duality proof done by hand:
R**→R :  {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  → ∀ x y → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y → R x y)   
R**→R {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/R f g leftInv/R₁} x y =
  λ z → transitive x (g (f y)) y
        (transitive x (g (f x)) (g (f y))
        (symmetric (g (f x)) x (leftInv/R₁ x)) z) (leftInv/R₁ y) 
        
R→R** :  {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  → ∀ x y → (R x y → R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y)   
R→R** {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/R f g leftInv/R₁} x y =
  λ z → transitive (g (f x)) y (g (f y))
        (transitive (g (f x)) x y (leftInv/R₁ x) z)
        (symmetric (g (f y)) y (leftInv/R₁ y)) 

R*-IsProp-Def1 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  {isp : ∀ x y → isProp (R x y)} → ∀ x y → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y) ≡ (R x y)
R*-IsProp-Def1 {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/r@(iso/R f g leftInv/R₁)} {isp} x y =
  isoToPath (iso (R**→R {iso/r = iso/r} x y) (R→R** {iso/r = iso/r} x y)
  (λ rxy → isp x y (R**→R {iso/r = iso/r} x y (R→R** {iso/r = iso/r} x y rxy)) rxy)
  λ rgf → isp (g (f x)) (g (f y)) (R→R** {iso/r = iso/r} x y (R**→R {iso/r = iso/r} x y rgf)) rgf) 

R**≡R : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  {isp : ∀ x y → isProp (R x y)} → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r}) ≡ R
R**≡R {ℓ} {A} {B} {R} ER@{equivRel reflexive symmetric transitive} {iso/r@(iso/R f g leftInv/R₁)} {isp} i x y = help x y i
   where
     isp' : isProp (R x y)
     isp' = isp x y
     help : (x' y' : A) → R* {R = R* {iso/r = iso/r}} {ER = isEquivRelR* A B {ER = ER}
       (iso/R f g leftInv/R₁)} {iso/r = iso/R g f λ a → leftInv/R₁ (g a)} x' y' ≡ R x' y'
     help = R*-IsProp-Def1 {iso/r = iso/r}{isp}  

--- A few more R* identity lemmas:
R*≡Rinv :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R A B {R} ER} →
 ∀ b b' → R* {ℓ}{ℓ}{A}{B}{R}{ER}{iso/r} b b' ≡ R (iso/r .inv/R b) (iso/r .inv/R b') 
R*≡Rinv b b' = refl

R*≡λttHlp :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{AB : A ≡ B} →
  ∀ b b' → R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB} b b' ≡ (R (transport (sym AB) b) (transport (sym AB) b')) 
R*≡λttHlp {ℓ}{A}{B}{R}{ER} {AB} b b' = isoToPath (iso (λ z → z) (λ z → z) (λ b₁ i → b₁) λ a i → a)
  where
    iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB
    defR* : R* {iso/r = iso/r} b b' ≡  R (iso/r .inv/R b) (iso/r .inv/R b')
    defR* = refl

R*≡λR :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R A B {R} ER} →
  R* {iso/r = iso/r} ≡ (λ b b' → R (iso/r .inv/R b) (iso/r .inv/R b')) 
R*≡λR {ℓ}{A}{B}{R}{ER}{iso/r} = λ i b b' → R*≡Rinv {ℓ}{A}{B}{R}{ER}{iso/r} b b' i

R*≡λtt :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{AB : A ≡ B} →
  R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB} ≡ (λ b b' → R (transport (sym AB) b) (transport (sym AB) b')) 
R*≡λtt {ℓ}{A}{B}{R}{ER}{AB} = λ i b b' → R*≡λttHlp {ℓ}{A}{B}{R}{ER}{AB} b b' i

---------------

-- Definitions, functions and lemmas concerning A/R as a set quotient:
A/R→B/R* : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  (aᵣ : A / R) → B / R* {iso/r = iso/r}
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} [ a ] =  _/_.[ iso/r .fun/R  a ]
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} (eq/ a a' r i) = _/_.eq/ (iso/r .fun/R a) (iso/r .fun/R a') (R→R* {iso/r = iso/r} r) i
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} (squash/ a a' p q i j) = squash/ (A/R→B/R* {iso/r = iso/r} a) (A/R→B/R* {iso/r = iso/r} a')
  (cong (λ u → A/R→B/R* {iso/r = iso/r} u) p) (cong (λ u → A/R→B/R* {iso/r = iso/r} u) q) i j

B/R*→A/R : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  (bᵣ : B / R* {iso/r = iso/r}) → A / R
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} [ b ] =  _/_.[ iso/r .inv/R  b ]
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} (eq/ b b' r i) = eq/ (iso/r .inv/R b) (iso/r .inv/R b') r i
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} (squash/ b b' p q i j) =
  squash/ (B/R*→A/R {iso/r = iso/r} b) (B/R*→A/R {iso/r = iso/r} b')
  (cong (λ u → B/R*→A/R {iso/r = iso/r} u) p) (cong (λ u → B/R*→A/R {iso/r = iso/r} u) q) i j

raa'→[a]≡[a'] : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {a a' : A} → R a a' → (_≡_) {ℓ} {A / R} (_/_.[ a ]) (_/_.[ a' ]) 
raa'→[a]≡[a'] {ℓ} {A} {R} {a} {a'} raa' = _/_.eq/ a a' raa' 

∥f∥₁-map : {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → ∥ A ∥₁ → ∥ B ∥₁   
∥f∥₁-map {ℓ} {ℓ'} {A} {B} f A' = A' >>= λ a → return (f a)

extrapolate[] : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} →
  (f : (A / R) → (A / R)) → (∀ (a : A) → f [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → ∥ f aᵣ ≡ aᵣ ∥₁ 
extrapolate[] {ℓ} {A} {R} f fa aᵣ = ∥f∥₁-map (λ z → z .snd) goal
                  where
                    a[] : ∀ (aᵣ : A / R) → ∥ A ∥₁
                    a[] aᵣ = ∥f∥₁-map fst ([]surjective aᵣ)
                    a[]* : ∥ Σ A (λ a → [ a ] ≡ aᵣ) ∥₁              
                    a[]* = []surjective aᵣ
                    step1 : Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f [ a ] ≡ aᵣ)
                    step1 (fst₁ , snd₁) = fst₁ , ((fa fst₁) ∙ snd₁)
                    step2 : Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f aᵣ ≡ f [ a ]) 
                    step2 (fst₁ , snd₁) = fst₁ , (sym (cong f snd₁))
                    stepf :  Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f aᵣ ≡ aᵣ)
                    stepf (fst₁ , snd₁) = fst₁ , (snd (step2 (fst₁ , snd₁))) ∙ (snd (step1 (fst₁ , snd₁)))
                    goal : ∥ Σ A (λ a → f aᵣ ≡ aᵣ) ∥₁
                    goal = ∥f∥₁-map stepf a[]*

isoA/R-B/R'Hlp3 : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} →
  (f : (A / R) → (A / R)) → (∀ (a : A) → f [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → f aᵣ ≡ aᵣ
isoA/R-B/R'Hlp3 {ℓ} {A} {R} f fid aᵣ = rec (squash/ (f aᵣ) aᵣ) (λ u → u) (extrapolate[] {ℓ}{A}{R} f fid aᵣ)

isoA/R-B/R'Hlp1 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}
  → (iso/r : Iso/R {ℓ} A B {R} ER) → (aᵣ : A / R)
  → (B/R*→A/R {iso/r = iso/r} (A/R→B/R* {iso/r = iso/r} aᵣ)) ≡ aᵣ 
isoA/R-B/R'Hlp1 {ℓ} {A} {B} {R} ER@{equivRel rf sm trns} iso/r@(iso/R f g rgfa≡a) aᵣ =
  step2 (λ x → B/R*→A/R {iso/r = iso/r} (A/R→B/R* {iso/r = iso/r} x)) (λ a → step1 a) aᵣ
    where
      help1 : ∀ (a : A) → R (g (f a)) a
      help1 a = rgfa≡a a
      step1 : ∀ (a : A) → [ g (f a) ] ≡ [ a ]
      step1 a = raa'→[a]≡[a'] (help1 a)
      step2 : (f' : (A / R) → (A / R)) → (∀ (a : A) → f' [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → f' aᵣ ≡ aᵣ
      step2 f' x aᵣ i = isoA/R-B/R'Hlp3 f' x aᵣ i  

isoA/R-B/R'Hlp2 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}
  → (iso/r : Iso/R {ℓ} A B {R} ER) → (bᵣ : B / R* {iso/r = iso/r})
  → (A/R→B/R* {iso/r = iso/r} (B/R*→A/R {iso/r = iso/r} bᵣ)) ≡ bᵣ 
isoA/R-B/R'Hlp2 {ℓ} {A} {B} {R} ER@{equivRel rf sm trns} iso/r@(iso/R f g rgfa≡a) bᵣ =
  step2 (λ x → A/R→B/R* {iso/r = iso/r} (B/R*→A/R {iso/r = iso/r} x)) (λ b → step1 b) bᵣ
    where
      help1 : ∀ (a : A) → R (g (f a)) a
      help1 a = rgfa≡a a
      help2 : ∀ (b : B) → (R* {iso/r = iso/r} (f (g b))) b
      help2 = λ b → rgfa≡a (g b)
      step1 : ∀ (b : B) → (_≡_) {A = B / R* {iso/r = iso/r}} [ f (g b) ] [ b ]   
      step1 b =  raa'→[a]≡[a'] (help2 b)
      step2 : (g' : (B / R* {iso/r = iso/r}) → (B / R* {iso/r = iso/r})) → (∀ (b : B) → g' [ b ] ≡ [ b ]) →
        ∀ (bᵣ : B / R* {iso/r = iso/r}) → g' bᵣ ≡ bᵣ
      step2 g' x bᵣ i = isoA/R-B/R'Hlp3 g' x bᵣ i 

-- An important set quotient isomorphism:
isoA/R-B/R' : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  Iso (A / R) (B / R* {iso/r = iso/r})
isoA/R-B/R' {ℓ}{A}{B}{R}{ER}{iso/r} = iso (A/R→B/R* {iso/r = iso/r})
  (B/R*→A/R {iso/r = iso/r}) (λ b → isoA/R-B/R'Hlp2 iso/r b) λ a → isoA/R-B/R'Hlp1 iso/r a

---------------
-- An important set quotient equality lemma:
quotientEqualityLemma : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
                 → A / R ≡ B / (R* {iso/r = iso/r})
quotientEqualityLemma {ℓ} {A}{B}{R}{ER}{iso/r} = isoToPath (isoA/R-B/R' {ℓ}{A}{B}{R}{ER}{iso/r})
----

-- Another set quotient equality lemma relying on Rel R and Rel R' propositionality:
A/R≡A/R'Hlp : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (ispR : ∀ a a' → isProp (R a a')) →
  (ispR' : ∀ a a' → isProp (R' a a')) →
  (RR' : ∀ a a' → R a a' → R' a a') → (R'R : ∀ a a' → R' a a' → R a a') → A / R ≡ A / R'
A/R≡A/R'Hlp {ℓ} {A}{R}{R'} ispR ispR' RR' R'R = cong (λ u → A / u) R≡R'
  where
    Rxy≡R'xy : ∀ x y → R x y ≡ R' x y
    Rxy≡R'xy x y = isoToPath (iso (RR' x y) (R'R x y)
      (λ b → ispR' x y (RR' x y (R'R x y b)) b) (λ a → ispR x y (R'R x y (RR' x y a)) a))
    R≡R' : R ≡ R'
    R≡R' = funExt (λ x → funExt (λ y → Rxy≡R'xy x y))

-- A simpler version:
quotientRule : {A : Type ℓ} → {R R' : A → A → Type ℓ} → (RR' : R ≡ R') → A / R ≡ A / R'
quotientRule {ℓ} {A}{R}{R'} RR' i = A / (RR' i)

A/R≡A/R'Hlp2 : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (RR' : ∀ a a' → (R a a' → R' a a')) → (R'R : ∀ a a' → (R' a a' → R a a')) → A / (λ a b → ∥ R a b ∥₁) ≡ A / (λ a b → ∥ R' a b ∥₁)
A/R≡A/R'Hlp2 {ℓ} {A}{R}{R'} RR' R'R = A/R≡A/R'Hlp (λ a a' → isPropPropTrunc) (λ a a' → isPropPropTrunc) (λ a a' raa' → ∥f∥₁-map (RR' a a') raa') (λ a a' r'aa' → ∥f∥₁-map (R'R a a') r'aa')

-- The propositional truncation of R makes no difference to the resulting quotient,
-- and so we have the following quotient equality lemma:
truncRel≡ : {A : Type ℓ}{R : A → A → Type ℓ} → (A / R) ≡ (A / (λ a b → ∥ R a b ∥₁))
truncRel≡ {ℓ}{A}{R} = isoToPath truncRelIso

-- A stronger quotient equality lemma based on the preceding, consistent with intuition:
A/R≡A/R' : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (RR' : ∀ a a' → (R a a' → R' a a')) → (R'R : ∀ a a' → (R' a a' → R a a')) → A / R ≡ A / R'
A/R≡A/R' {ℓ} {A}{R}{R'} RR' R'R = truncRel≡ ∙ (A/R≡A/R'Hlp2 RR' R'R) ∙ sym truncRel≡

-- We can also obtain the following quotient equality lemmas:
quotientEqualityLemma2 : {A B : Type ℓ}{R : A → A → Type ℓ}{ER : isEquivRel R} →
  (AB : A ≡ B) → (A / R) ≡ (B / λ b b' → R (transport (sym AB) b) (transport (sym AB) b'))
quotientEqualityLemma2 {ℓ}{A}{B}{R}{ER} AB = quotientEqualityLemma {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB}
  where
    lemma : (A / R) ≡ (B / R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB})
    lemma = quotientEqualityLemma {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB} 

quotientEqualityLemma3 : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{R' : B → B → Type ℓ}
                 {ER : isEquivRel R} →
                 (iso/r : Iso/R {ℓ} A B {R} ER) → 
                 (R'→R* : ∀ b b' → (R' b b' → R* {iso/r = iso/r} b b')) →
                 (R*→R' : ∀ b b' → (R* {iso/r = iso/r} b b' → R' b b')) →
                 A / R ≡ B / R'
quotientEqualityLemma3 {ℓ} {A}{B}{R}{R'}{ER} iso/r R'→R* R*→R' = step1 ∙ A/R≡A/R' R*→R' R'→R* 
  where
    step1 : (A / R) ≡ (B / R* {iso/r = iso/r})
    step1 = quotientEqualityLemma {ℓ}{A}{B}{R}{ER}{iso/r}
  
quotientEqualityLemma4 : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{R' : B → B → Type ℓ}
                 {ER : isEquivRel R} →
                 (iso/r : Iso/R {ℓ} A B {R} ER) → 
                 (R'→Rinv : ∀ b b' → (R' b b' → R (iso/r .inv/R b) (iso/r .inv/R b'))) →
                 (Rinv→R' : ∀ b b' → (R (iso/r .inv/R b) (iso/r .inv/R b') → R' b b')) →
                 A / R ≡ B / R'
quotientEqualityLemma4 {ℓ} {A}{B}{R}{R'}{ER} iso/r R'→R R→R' =
  step1 ∙ A/R≡A/R' (λ b b' z → R→R' b b' z) (λ b b' x → R'→R b b' x)
    where
      help :  ∀ b b' → R* {ℓ}{ℓ}{A}{B}{R}{ER}{iso/r} b b' ≡ R (iso/r .inv/R b) (iso/r .inv/R b')
      help b b' = refl 
      step1 : (A / R) ≡ (B / R* {iso/r = iso/r})
      step1 = quotientEqualityLemma {ℓ}{A}{B}{R}{ER}{iso/r}

    
