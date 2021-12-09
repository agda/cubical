{-
The finite system is the underlying graph/category of finite projective limits
-}

{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Finite.FiniteSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Categories.Category


data FinSysType (n : ℕ) : Type where
 sing : Fin n → FinSysType n
 pair : Fin n → Fin n → FinSysType n


open Category

FinSysCat : ℕ → Category ℓ-zero ℓ-zero
ob (FinSysCat n) = FinSysType n
Hom[_,_] (FinSysCat n) (sing i) (sing j) = i ≡ j
Hom[_,_] (FinSysCat n) (sing i) (pair j k) = (i ≡ j) ⊎ (i ≡ k)
Hom[_,_] (FinSysCat n) (pair i j) (sing k) = ⊥
Hom[_,_] (FinSysCat n) (pair i j) (pair k l) = (i ≡ k) × (j ≡ l)
id (FinSysCat n) {x = sing _} = refl
id (FinSysCat n) {x = pair _ _} = refl , refl
_⋆_ (FinSysCat n) {x = sing _} {y = sing _} {z = sing _} p q = p ∙ q
_⋆_ (FinSysCat n) {x = sing _} {y = sing _} {z = pair _ _} p (inl q) = inl (p ∙ q)
_⋆_ (FinSysCat n) {x = sing _} {y = sing _} {z = pair _ _} p (inr q) = inr (p ∙ q)
_⋆_ (FinSysCat n) {x = sing _} {y = pair _ _} {z = pair _ _} (inl p) (q , r) = inl (p ∙ q)
_⋆_ (FinSysCat n) {x = sing _} {y = pair _ _} {z = pair _ _} (inr p) (q , r) = inr (p ∙ r)
_⋆_ (FinSysCat n) {x = pair _ _} {y = pair _ _} {z = pair _ _} (p , q) (r , s) = p ∙ r , q ∙ s
⋆IdL (FinSysCat n) {x = sing _} {y = sing _} p = sym (lUnit p)
⋆IdL (FinSysCat n) {x = sing _} {y = pair _ _} (inl p) = cong inl (sym (lUnit p))
⋆IdL (FinSysCat n) {x = sing _} {y = pair _ _} (inr p) = cong inr (sym (lUnit p))
⋆IdL (FinSysCat n) {x = pair _ _} {y = pair _ _} (p , q) = cong₂ _,_ (sym (lUnit p)) (sym (lUnit q))
⋆IdR (FinSysCat n) {x = sing _} {y = sing _} p = sym (rUnit p)
⋆IdR (FinSysCat n) {x = sing _} {y = pair _ _} (inl p) = cong inl (sym (rUnit p))
⋆IdR (FinSysCat n) {x = sing _} {y = pair _ _} (inr p) = cong inr (sym (rUnit p))
⋆IdR (FinSysCat n) {x = pair _ _} {y = pair _ _} (p , q) = cong₂ _,_ (sym (rUnit p)) (sym (rUnit q))
⋆Assoc (FinSysCat n) {x = sing _} {y = sing _} {z = sing _} {w = sing _} p q r = sym (assoc p q r)
⋆Assoc (FinSysCat n) {x = sing _} {y = sing _} {z = sing _} {w = pair _ _} p q (inl r) =
       cong inl (sym (assoc p q r))
⋆Assoc (FinSysCat n) {x = sing _} {y = sing _} {z = sing _} {w = pair _ _} p q (inr r) =
       cong inr (sym (assoc p q r))
⋆Assoc (FinSysCat n) {x = sing _} {y = sing _} {z = pair _ _} {w = pair _ _} p (inl q) (r , s) =
       cong inl (sym (assoc p q r))
⋆Assoc (FinSysCat n) {x = sing _} {y = sing _} {z = pair _ _} {w = pair _ _} p (inr q) (r , s) =
       cong inr (sym (assoc p q s))
⋆Assoc (FinSysCat n) {x = sing _} {y = pair _ _} {z = pair _ _} {w = pair _ _}
       (inl p) (q , r) (s , t) = cong inl (sym (assoc p q s))
⋆Assoc (FinSysCat n) {x = sing _} {y = pair _ _} {z = pair _ _} {w = pair _ _}
       (inr p) (q , r) (s , t) = cong inr (sym (assoc p r t))
⋆Assoc (FinSysCat n) {x = pair _ _} {y = pair _ _} {z = pair _ _} {w = pair _ _}
       (p , q) (r , s) (t , u) = cong₂ _,_ (sym (assoc p r t)) (sym (assoc q s u))
isSetHom (FinSysCat n) {x = sing _} {y = sing _} = isProp→isSet (isSetFin _ _)
isSetHom (FinSysCat n) {x = sing _} {y = pair _ _} = isSet⊎ (isProp→isSet (isSetFin _ _))
                                                            (isProp→isSet (isSetFin _ _))
isSetHom (FinSysCat n) {x = pair _ _} {y = sing _} = isProp→isSet isProp⊥
isSetHom (FinSysCat n) {x = pair _ _} {y = pair _ _} = isSetΣ (isProp→isSet (isSetFin _ _))
                                                              (λ _ → isProp→isSet (isSetFin _ _))
