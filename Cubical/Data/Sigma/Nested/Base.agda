{-

This file contains definition of:
 
 - Sig - array of type families where conseciutive ones can depend on previous 
 - NestedΣᵣ - Type of "rightmost" nested Sigmas, parametrised by Sig

 - isomorphism of concatenation and spliting of signature and coresponding NesteΣ

 - isomorphism giving easy acess to last type in signature, and last "field" in
   NestedΣ

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Base where

open import Cubical.Data.Nat

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

-- Sig comes from "Signature" (I am not shure if this name is OK)
-- this type descirbes array of n Types, (Type families?) where k-th can
-- depend on all previous.
-- Something similiar (but with more features, and other (i presume) goals) is defined
-- in std-lib in src/Data/Record.agda,
-- in std-lib implementation
-- next signature is defined as a Pair of:
-- * shorter signature
-- * Type parametrised by Record of this signature 
--
-- here the next Sig shape is defined in "oposite way",
-- as pair of:
-- * Type
-- * and function from this Type into shorter signatures
--
-- sig-n+1-iso can be used to show that those definitions are isomorphic
-- should I include such isomorphism ?
--
--


Sig : ∀ ℓ → ℕ →  Type (ℓ-suc ℓ)
Sig ℓ zero = Lift Unit
Sig ℓ (suc zero) = Type ℓ
Sig ℓ (suc (suc n)) = Σ (Type ℓ) λ x → x → Sig ℓ (suc n)


-- This file only defines NestedΣ in one particular "shape" - rightmost
-- , meaning that next nested sigma is always in the second argument of outer one. 
-- Definitions with "ᵣ" potfix, marks functions to work with this "default" rightmost shape

NestedΣᵣ : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type ℓ
NestedΣᵣ {n = zero} _ = Lift Unit
NestedΣᵣ {n = suc zero} Ty = Ty
NestedΣᵣ {n = suc (suc n)} (Ty , →Sig) = Σ Ty (NestedΣᵣ ∘ →Sig)




-- those four basic helpers sometimes helps to avoid some case splitting

prependTyᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → (A → Sig ℓ n) → Sig ℓ (suc n)
prependTyᵣ {n = zero} {A} _ = A
prependTyᵣ {n = suc n} = _ ,_ 


popTyᵣ : ∀ {ℓ} → ∀ {n} 
           → Sig ℓ (suc n)
           → Σ[ A ∈  Type ℓ ] (A → Sig ℓ n)
           
popTyᵣ {n = zero} x = x , (const _)
popTyᵣ {n = suc n} x = fst x , snd x

prependValᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)
                → (x : A)
                → NestedΣᵣ (s x)
                → NestedΣᵣ (prependTyᵣ {n = n} s)
prependValᵣ {n = zero} s x _ = x
prependValᵣ {n = suc n} s = _,_


popValᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)                
                → NestedΣᵣ (prependTyᵣ {n = n} s)
                → Σ[ x ∈ A ] NestedΣᵣ (s x)
                 
popValᵣ {n = zero} s x = x , _
popValᵣ {n = suc n} s x = x






-- * sig-split-concat-Iso
--   relates Sig (n + m) and Σ[ sₙ ∈ Sig n ] (NestedΣᵣ sₙ →  Sig ℓ m) 
--   this isomorphism is used later in file "Nested.agda" to define
--   NestedΣ of diferent than "rightmost" shapes


sig-concat : ∀ {ℓ} → ∀ {n m}
           → (sₙ : Sig ℓ n)
           → (sₘ : NestedΣᵣ sₙ →  Sig ℓ m)
           → Sig ℓ (n + m)
sig-concat {n = zero} sₙ sₘ = sₘ _
sig-concat {n = suc zero} {m} sₙ sₘ = prependTyᵣ {n = m} {A = sₙ} sₘ
sig-concat {n = suc (suc n)} {m} sₙ sₘ =
   prependTyᵣ {n = (suc n) + m}
     λ x → sig-concat {n = suc n} {m} (snd sₙ x) (sₘ ∘ (x ,_)) 

sig-split : ∀ {ℓ} → ∀ {n m}
           → Sig ℓ (n + m)
           → Σ[ sₙ ∈  Sig ℓ n ] (NestedΣᵣ sₙ → Sig ℓ m)
sig-split {n = zero} x = _ , const x
sig-split {n = suc zero} {zero} = _, _
sig-split {n = suc zero} {suc m} = idfun _
sig-split {n = suc (suc n)} x =
  let z = λ (y : fst x) → sig-split {n = suc n} (snd x y)
  in (fst x , fst ∘ z) ,  uncurry (snd ∘ z)

section-split-concat : ∀ {ℓ} → ∀ {n m}
    → section sig-split (uncurry (sig-concat {ℓ} {n} {m}))
section-split-concat {n = zero} b = refl
section-split-concat {n = suc zero} {zero} b = refl
section-split-concat {n = suc zero} {suc m} b = refl
section-split-concat {n = suc (suc n)} {m} b i =
  let z = λ (y : fst (fst b)) →
            section-split-concat (snd (fst b) y , snd b ∘ (y ,_)) i
  in ((fst (fst b)) ,  fst ∘ z) , uncurry (snd ∘ z)

retract-split-concat : ∀ {ℓ} → ∀ {n m}
    → retract sig-split (uncurry (sig-concat {ℓ} {n} {m}))
retract-split-concat {n = zero} a = refl
retract-split-concat {n = suc zero} {zero} a = refl
retract-split-concat {n = suc zero} {suc m} a = refl
retract-split-concat {n = suc (suc n)} {m} a i =
  prependTyᵣ λ (y : fst a) → retract-split-concat {n = suc n} {m} (snd a y) i

sig-split-concat-Iso : ∀ {ℓ} → ∀ {n m}
                   → Iso (Sig ℓ (n + m))
                         (Σ[ sₙ ∈  Sig ℓ n ] (NestedΣᵣ sₙ → Sig ℓ m))
sig-split-concat-Iso {ℓ} {n} {m} =
  iso (sig-split)
      (uncurry sig-concat)
      (section-split-concat)
      (retract-split-concat {n = n})


nestedΣᵣ-split :  ∀ {ℓ} → ∀ {n m} 
                       → (s : Sig ℓ (n + m))
                       → NestedΣᵣ s
                       → Σ (NestedΣᵣ (fst (sig-split {n = n} s)))
                           (NestedΣᵣ ∘ (snd (sig-split {n = n} {m = m} s))) 
nestedΣᵣ-split {n = zero} s x = _ , x
nestedΣᵣ-split {n = suc zero} {zero} s = _, _
nestedΣᵣ-split {n = suc zero} {suc m} s x = x
nestedΣᵣ-split {n = suc (suc n)} {m} s x =
   _ , snd (nestedΣᵣ-split {n = suc n} ((snd s) (fst x)) (snd x))

nestedΣᵣ-concat :  ∀ {ℓ} → ∀ {n m} 
                       → (sₙ : Sig ℓ n)
                       → (sₘ : NestedΣᵣ sₙ →  Sig ℓ m)
                       → Σ (NestedΣᵣ sₙ) (NestedΣᵣ ∘ sₘ)
                       → NestedΣᵣ (sig-concat sₙ sₘ)
nestedΣᵣ-concat {n = zero} sₙ sₘ = snd
nestedΣᵣ-concat {n = suc zero} {m} sₙ sₘ = prependValᵣ sₘ _ ∘ snd
nestedΣᵣ-concat {n = suc (suc n)} {m} sₙ sₘ x =
     prependValᵣ {n = suc n + m} (_) _
      (nestedΣᵣ-concat {n = suc n} _ _ (_ , snd x))

nestedΣᵣ-split' :  ∀ {ℓ} → ∀ {n m} 
                       → (sₙ :  Sig ℓ n )
                       → (sₘ : NestedΣᵣ sₙ → Sig ℓ m)
                       → NestedΣᵣ (sig-concat sₙ sₘ)
                       → Σ (NestedΣᵣ sₙ) (NestedΣᵣ ∘ sₘ) 
nestedΣᵣ-split' {n = zero} sₙ sₘ = _ ,_
nestedΣᵣ-split' {n = suc zero} {zero} sₙ sₘ = _, _
nestedΣᵣ-split' {n = suc zero} {suc m} sₙ sₘ = idfun _
nestedΣᵣ-split' {n = suc (suc n)} {m} sₙ sₘ (a , x) =
 let (fs , sn) = nestedΣᵣ-split' {n = suc n} {m} _ _ x 
 in (a , fs) , sn
  
nestedΣᵣ-concat' :  ∀ {ℓ} → ∀ {n m} 
                       → (s : Sig ℓ (n + m))
                       → Σ (NestedΣᵣ (fst (sig-split {n = n} s)))
                           (NestedΣᵣ ∘ (snd (sig-split {n = n} {m = m} s)))
                       → NestedΣᵣ s
nestedΣᵣ-concat' {n = zero} s = snd
nestedΣᵣ-concat' {n = suc zero} {zero} s = fst
nestedΣᵣ-concat' {n = suc zero} {suc m} s x = x
nestedΣᵣ-concat' {n = suc (suc n)} s ((a , x) , y) =
   a , nestedΣᵣ-concat' {n = suc n} (snd s a) (x , y)

nestedΣᵣ-concat-split-Iso : ∀ {ℓ} → ∀ {n m} 
                       → (s : Sig ℓ (n + m))
                       →  Iso
                        (Σ (NestedΣᵣ (fst (sig-split {n = n} s)))
                             (λ x → NestedΣᵣ (snd (sig-split {n = n} {m = m} s) x)))
                        (NestedΣᵣ s)
Iso.fun (nestedΣᵣ-concat-split-Iso {n = n} {m = m} s) = nestedΣᵣ-concat' {n = n} {m = m} s
Iso.inv (nestedΣᵣ-concat-split-Iso {n = n} {m = m} s) = nestedΣᵣ-split {n = n} {m = m} s
Iso.rightInv (nestedΣᵣ-concat-split-Iso {n = zero} s) b = refl
Iso.rightInv (nestedΣᵣ-concat-split-Iso {n = suc zero} {zero} s) b = refl
Iso.rightInv (nestedΣᵣ-concat-split-Iso {n = suc zero} {suc m} s) b = refl
Iso.rightInv (nestedΣᵣ-concat-split-Iso {n = suc (suc n)} {m} s) b =
  cong (_ ,_) (Iso.rightInv (nestedΣᵣ-concat-split-Iso {n = (suc n)} {m} ((snd s) (fst b))) (snd b))
Iso.leftInv (nestedΣᵣ-concat-split-Iso {n = zero} s) a = refl
Iso.leftInv (nestedΣᵣ-concat-split-Iso {n = suc zero} {zero} s) a = refl
Iso.leftInv (nestedΣᵣ-concat-split-Iso {n = suc zero} {suc m} s) a = refl
Iso.leftInv (nestedΣᵣ-concat-split-Iso {n = suc (suc n)} s) ((a , x) , y) =
 cong (λ (x' , y') → ((a , x') , y'))
    (Iso.leftInv (nestedΣᵣ-concat-split-Iso {n = suc n} (snd s a)) (x , y))





-- * sig-n+1-iso 
--   relates Sig ℓ (suc n) and Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1) 
--   this isomorphism is used later in file "Currying.agda" to
--   construct Sig-of-Sig, allowing to treat Sig as NestedΣ 


--TODO : try make n implicit ?
sig-n+1-split : ∀ {ℓ} → ∀ n → Sig ℓ (suc n) → Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1)
sig-n+1-split zero s =  _ , const s
sig-n+1-split 1 s = s
sig-n+1-split (suc (suc n)) s =
  let z : (fst s) → _
      z x = sig-n+1-split (suc n) (snd s x)

  in (fst s , fst ∘ z ) , uncurry (snd ∘ z)

sig-n+1-unsplit : ∀ {ℓ} → ∀ n → Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1) → Sig ℓ (suc n) 
sig-n+1-unsplit zero x = snd x _
sig-n+1-unsplit (suc zero) x = x
sig-n+1-unsplit (suc (suc n)) (s , r→Ty) =
  (fst s) , λ x → sig-n+1-unsplit (suc n) ((snd s) x , r→Ty ∘ (x ,_))

sig-n+1-iso : ∀ {ℓ} → ∀ n → Iso (Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1)) (Sig ℓ (suc n)) 
Iso.fun (sig-n+1-iso n) = sig-n+1-unsplit n
Iso.inv (sig-n+1-iso n) = sig-n+1-split n
Iso.rightInv (sig-n+1-iso zero) b = refl
Iso.rightInv (sig-n+1-iso (suc zero)) b = refl
Iso.rightInv (sig-n+1-iso (suc (suc n))) (s , z) =
  cong ( s ,_ ) (funExt λ x → Iso.rightInv (sig-n+1-iso (suc n)) (z x))

Iso.leftInv (sig-n+1-iso zero) a = refl
Iso.leftInv (sig-n+1-iso (suc zero)) a = refl
Iso.leftInv (sig-n+1-iso (suc (suc n))) ((Ty , s) , r→Ty) i =
  let z : Ty → _
      z x = (Iso.leftInv (sig-n+1-iso (suc n))) (s x , (r→Ty ∘ (x ,_))) i

  in (Ty , fst ∘ z) , uncurry (snd ∘ z)

NestedΣᵣ-n+1-split-iso : ∀ {ℓ} → ∀ n → (s : Sig ℓ (suc n)) →
                        Iso (NestedΣᵣ s) (Σ _ (snd (sig-n+1-split n s)))
NestedΣᵣ-n+1-split-iso zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
NestedΣᵣ-n+1-split-iso 1 s = idIso
NestedΣᵣ-n+1-split-iso {ℓ} (suc (suc n)) s =
 let prev = NestedΣᵣ-n+1-split-iso {ℓ} (suc n) in 
 iso (λ r → let (fs , se) = Iso.fun (prev ((snd s) (fst r))) (snd r)
            in (fst r , fs) , se )
     (λ r → fst (fst r) , Iso.inv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r))
     (λ r i → let (fs , se) = Iso.rightInv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r) i
              in (fst (fst r) , fs) , se)
     λ r i →   let (fs , se) =
                     Iso.leftInv (prev ((snd s) (fst r))) (snd r) i
               in (fst r) , fs , se

NestedΣᵣ-n+1-unsplit-iso : ∀ {ℓ} → ∀ n →
                         (s-r  : Σ (Sig ℓ n) λ z → NestedΣᵣ z → Sig ℓ 1) →
                          Iso (NestedΣᵣ (sig-n+1-unsplit {ℓ} n s-r)) (Σ _ (snd s-r))
NestedΣᵣ-n+1-unsplit-iso zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
NestedΣᵣ-n+1-unsplit-iso 1 s = idIso
Iso.fun (NestedΣᵣ-n+1-unsplit-iso (suc (suc n)) s-r) r =
  let (fs , se) = Iso.fun (NestedΣᵣ-n+1-unsplit-iso (suc n)
            ((snd (fst s-r) (fst r)) , (snd s-r) ∘ ( fst r ,_))) (snd r )

  in ((fst r) , fs) , se
Iso.inv (NestedΣᵣ-n+1-unsplit-iso (suc (suc n)) s) ((_ , _) , b) =
  _ , Iso.inv (NestedΣᵣ-n+1-unsplit-iso (suc n) (_ , snd s ∘ (_ ,_))) (_ , b)
Iso.rightInv (NestedΣᵣ-n+1-unsplit-iso (suc (suc n)) s) ((a , r) , b) i =
  let z = Iso.rightInv (NestedΣᵣ-n+1-unsplit-iso (suc n) (snd (fst s) a , snd s ∘ (a ,_)))
               (r , b) i
  in (a , fst z) , snd z
Iso.leftInv (NestedΣᵣ-n+1-unsplit-iso (suc (suc n)) s) (_ , r) =
  cong (_ ,_) (Iso.leftInv (NestedΣᵣ-n+1-unsplit-iso (suc n) _ ) r)
