{-

This file contains definition of:
 
 - Sig - array of type families where conseciutive ones can depend on previous 
 - NestedΣᵣ - Type of "right-most" nested Sigmas, parametrised by Sig

 - isomorphism of concatenation and spliting of Sig and coresponding NestedΣᵣ

 - isomorphism giving easy acess to last type in Sig, and last "field" in
   NestedΣᵣ

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Base where

open import Cubical.Data.Nat

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

-- Sig comes from "Signature" (I am not shure if this name is waranted here)
-- this type descirbes array of n Types, (Type families?) where k-th can
-- depend on all previous.
-- Something similiar (but with more features, and other (i presume) goals) is defined
-- in std-lib in src/Data/Record.agda,
-- in std-lib implementation
-- next signature is defined as a Pair of:
-- * shorter signature
-- * Type parametrised by Record of this signature 
-- (https://github.com/agda/agda-stdlib/blob/eeb731977da2daa079563e3d1d43b9e70d8f919a/src/Data/Record.agda#L56)
--
-- here the next signature is defined in "oposite way",
-- as pair of:
-- * Type
-- * and function from this Type into shorter signatures
--
-- sig-n+1-iso can be used to show that those definitions are isomorphic
-- should I include such isomorphism ?
--
--


Sig : ∀ ℓ → ℕ →  Type (ℓ-suc ℓ)
Sig ℓ 0 = Lift Unit
Sig ℓ 1 = Type ℓ
Sig ℓ (suc (suc n)) = Σ (Type ℓ) λ x → x → Sig ℓ (suc n)


-- This file only defines NestedΣ in one particular "shape" - rightmost
-- , meaning that next nested sigma is always in the second argument of outer one. 
-- Definitions with "ᵣ" postfix, marks functions to work with this "default" rightmost shape

NestedΣᵣ : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type ℓ
NestedΣᵣ {n = 0} _ = Lift Unit
NestedΣᵣ {n = 1} Ty = Ty
NestedΣᵣ {n = suc (suc n)} (Ty , →Sig) = Σ Ty (NestedΣᵣ ∘ →Sig)




-- those four basic helpers sometimes helps to avoid some case splitting near n = 0

prependTyᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → (A → Sig ℓ n) → Sig ℓ (suc n)
prependTyᵣ {n = 0} {A} _ = A
prependTyᵣ {n = suc n} = _ ,_ 


popTyᵣ : ∀ {ℓ} → ∀ {n} 
           → Sig ℓ (suc n)
           → Σ[ A ∈  Type ℓ ] (A → Sig ℓ n)
           
popTyᵣ {n = 0} x = x , (const _)
popTyᵣ {n = suc n} x = fst x , snd x

prependValᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)
                → (x : A)
                → NestedΣᵣ (s x)
                → NestedΣᵣ (prependTyᵣ {n = n} s)
prependValᵣ {n = 0} s x _ = x
prependValᵣ {n = suc n} s = _,_


popValᵣ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)                
                → NestedΣᵣ (prependTyᵣ {n = n} s)
                → Σ[ x ∈ A ] NestedΣᵣ (s x)
                 
popValᵣ {n = 0} s x = x , _
popValᵣ {n = suc n} s x = x





-- * sig-split-concat-Iso
--   relates Sig (n + m) and Σ[ sₙ ∈ Sig n ] (NestedΣᵣ sₙ →  Sig ℓ m) 
--   this isomorphism is used later in file "Nested.agda" to define
--   NestedΣ of diferent than "rightmost" shapes


module sig-cs where

  concat : ∀ {ℓ} → ∀ {n m}
             → (sₙ : Sig ℓ n)
             → (sₘ : NestedΣᵣ sₙ →  Sig ℓ m)
             → Sig ℓ (n + m)
  concat {n = 0} sₙ sₘ = sₘ _
  concat {n = 1} {m} sₙ sₘ = prependTyᵣ {n = m} {A = sₙ} sₘ
  concat {n = suc (suc n)} {m} sₙ sₘ =
     prependTyᵣ {n = (suc n) + m}
       λ x → concat {n = suc n} {m} (snd sₙ x) (sₘ ∘ (x ,_)) 

  split : ∀ {ℓ} → ∀ {n m}
             → Sig ℓ (n + m)
             → Σ[ sₙ ∈  Sig ℓ n ] (NestedΣᵣ sₙ → Sig ℓ m)
  split {n = 0} x = _ , const x
  split {n = 1} {0} = _, _
  split {n = 1} {suc m} = idfun _
  split {n = suc (suc n)} x =
    let z = λ (y : fst x) → split {n = suc n} (snd x y)
    in (fst x , fst ∘ z) ,  uncurry (snd ∘ z)

  split-concat : ∀ {ℓ} → ∀ {n m}
      → section split (uncurry (concat {ℓ} {n} {m}))
  split-concat {n = 0} b = refl
  split-concat {n = 1} {0} b = refl
  split-concat {n = 1} {suc m} b = refl
  split-concat {n = suc (suc n)} {m} b i =
    let z = λ (y : fst (fst b)) →
              split-concat (snd (fst b) y , snd b ∘ (y ,_)) i
    in ((fst (fst b)) ,  fst ∘ z) , uncurry (snd ∘ z)

  concat-split : ∀ {ℓ} → ∀ {n m}
      → retract split (uncurry (concat {ℓ} {n} {m}))
  concat-split {n = 0} a = refl
  concat-split {n = 1} {0} a = refl
  concat-split {n = 1} {suc m} a = refl
  concat-split {n = suc (suc n)} {m} a i =
    prependTyᵣ λ (y : fst a) → concat-split {n = suc n} {m} (snd a y) i

  isom : ∀ {ℓ} → ∀ {n m}
                     → Iso (Sig ℓ (n + m))
                           (Σ[ sₙ ∈  Sig ℓ n ] (NestedΣᵣ sₙ → Sig ℓ m))
  isom {ℓ} {n} {m} =
    iso (split)
        (uncurry concat)
        (split-concat)
        (concat-split {n = n})


-- isomorphism of NestedΣᵣ related to concat-split isomorphism of Sig

module nestedΣᵣ-cs where


  split :  ∀ {ℓ} → ∀ {n m} 
                         → (s : Sig ℓ (n + m))
                         → NestedΣᵣ s
                         → Σ (NestedΣᵣ (fst (sig-cs.split {n = n} s)))
                             (NestedΣᵣ ∘ (snd (sig-cs.split {n = n} {m = m} s))) 
  split {n = 0} s x = _ , x
  split {n = 1} {0} s = _, _
  split {n = 1} {suc m} s x = x
  split {n = suc (suc n)} {m} s x =
     _ , snd (split {n = suc n} ((snd s) (fst x)) (snd x))

  concat :  ∀ {ℓ} → ∀ {n m} 
                         → (sₙ : Sig ℓ n)
                         → (sₘ : NestedΣᵣ sₙ →  Sig ℓ m)
                         → Σ (NestedΣᵣ sₙ) (NestedΣᵣ ∘ sₘ)
                         → NestedΣᵣ (sig-cs.concat sₙ sₘ)
  concat {n = 0} sₙ sₘ = snd
  concat {n = 1} {m} sₙ sₘ = prependValᵣ sₘ _ ∘ snd
  concat {n = suc (suc n)} {m} sₙ sₘ x =
       prependValᵣ {n = suc n + m} (_) _
        (concat {n = suc n} _ _ (_ , snd x))

  split' :  ∀ {ℓ} → ∀ {n m} 
                         → (sₙ :  Sig ℓ n )
                         → (sₘ : NestedΣᵣ sₙ → Sig ℓ m)
                         → NestedΣᵣ (sig-cs.concat sₙ sₘ)
                         → Σ (NestedΣᵣ sₙ) (NestedΣᵣ ∘ sₘ) 
  split' {n = 0} sₙ sₘ = _ ,_
  split' {n = 1} {0} sₙ sₘ = _, _
  split' {n = 1} {suc m} sₙ sₘ = idfun _
  split' {n = suc (suc n)} {m} sₙ sₘ (a , x) =
   let (fs , sn) = split' {n = suc n} {m} _ _ x 
   in (a , fs) , sn

  concat' :  ∀ {ℓ} → ∀ {n m} 
                         → (s : Sig ℓ (n + m))
                         → Σ (NestedΣᵣ (fst (sig-cs.split {n = n} s)))
                             (NestedΣᵣ ∘ (snd (sig-cs.split {n = n} {m = m} s)))
                         → NestedΣᵣ s
  concat' {n = 0} s = snd
  concat' {n = 1} {0} s = fst
  concat' {n = 1} {suc m} s x = x
  concat' {n = suc (suc n)} s ((a , x) , y) =
     a , concat' {n = suc n} (snd s a) (x , y)

  isom : ∀ {ℓ} → ∀ {n m} 
                         → (s : Sig ℓ (n + m))
                         →  Iso
                          (Σ (NestedΣᵣ (fst (sig-cs.split {n = n} s)))
                               (λ x → NestedΣᵣ (snd (sig-cs.split {n = n} {m = m} s) x)))
                          (NestedΣᵣ s)
  Iso.fun (isom {n = n} {m = m} s) = concat' {n = n} {m = m} s
  Iso.inv (isom {n = n} {m = m} s) = split {n = n} {m = m} s
  Iso.rightInv (isom {n = 0} s) b = refl
  Iso.rightInv (isom {n = 1} {0} s) b = refl
  Iso.rightInv (isom {n = 1} {suc m} s) b = refl
  Iso.rightInv (isom {n = suc (suc n)} {m} s) b =
    cong (_ ,_) (Iso.rightInv (isom {n = (suc n)} {m} ((snd s) (fst b))) (snd b))
  Iso.leftInv (isom {n = 0} s) a = refl
  Iso.leftInv (isom {n = 1} {0} s) a = refl
  Iso.leftInv (isom {n = 1} {suc m} s) a = refl
  Iso.leftInv (isom {n = suc (suc n)} s) ((a , x) , y) =
   cong (λ (x' , y') → ((a , x') , y'))
      (Iso.leftInv (isom {n = suc n} (snd s a)) (x , y))




-- -- * sig-n+1-iso 
-- --   relates Sig ℓ (suc n) and Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1) 
-- --   this isomorphism is used later in file "Currying.agda" to
-- --   construct Sig-of-Sig, allowing to treat Sig as NestedΣ 

module sig-n+1 where

  to : ∀ {ℓ} → ∀ n → Sig ℓ (suc n) → Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1)
  to 0 s =  _ , const s
  to 1 s = s
  to (suc (suc n)) s =
    let z : (fst s) → _
        z x = to (suc n) (snd s x)

    in (fst s , fst ∘ z ) , uncurry (snd ∘ z)

  from : ∀ {ℓ} → ∀ n → Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1) → Sig ℓ (suc n) 
  from 0 x = snd x _
  from 1 x = x
  from (suc (suc n)) (s , r→Ty) =
    (fst s) , λ x → from (suc n) ((snd s) x , r→Ty ∘ (x ,_))

  isom : ∀ {ℓ} → ∀ n → Iso (Σ (Sig ℓ n) (λ sₙ → NestedΣᵣ sₙ → Sig ℓ 1)) (Sig ℓ (suc n)) 
  Iso.fun (isom n) = from n
  Iso.inv (isom n) = to n
  Iso.rightInv (isom 0) b = refl
  Iso.rightInv (isom 1) b = refl
  Iso.rightInv (isom (suc (suc n))) (s , z) =
    cong ( s ,_ ) (funExt λ x → Iso.rightInv (isom (suc n)) (z x))

  Iso.leftInv (isom 0) a = refl
  Iso.leftInv (isom 1) a = refl
  Iso.leftInv (isom (suc (suc n))) ((Ty , s) , r→Ty) i =
    let z : Ty → _
        z x = (Iso.leftInv (isom (suc n))) (s x , (r→Ty ∘ (x ,_))) i

    in (Ty , fst ∘ z) , uncurry (snd ∘ z)

module nestedΣᵣ-n+1 where

  isom-to : ∀ {ℓ} → ∀ n → (s : Sig ℓ (suc n)) →
                          Iso (NestedΣᵣ s) (Σ _ (snd (sig-n+1.to n s)))
  isom-to zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
  isom-to 1 s = idIso
  isom-to {ℓ} (suc (suc n)) s =
   let prev = isom-to {ℓ} (suc n) in 
   iso (λ r → let (fs , se) = Iso.fun (prev ((snd s) (fst r))) (snd r)
              in (fst r , fs) , se )
       (λ r → fst (fst r) , Iso.inv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r))
       (λ r i → let (fs , se) = Iso.rightInv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r) i
                in (fst (fst r) , fs) , se)
       λ r i →   let (fs , se) =
                       Iso.leftInv (prev ((snd s) (fst r))) (snd r) i
                 in (fst r) , fs , se

  isom-from : ∀ {ℓ} → ∀ n →
                           (s-r  : Σ (Sig ℓ n) λ z → NestedΣᵣ z → Sig ℓ 1) →
                            Iso (NestedΣᵣ (sig-n+1.from {ℓ} n s-r)) (Σ _ (snd s-r))
  isom-from zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
  isom-from 1 s = idIso
  Iso.fun (isom-from (suc (suc n)) s-r) r =
    let (fs , se) = Iso.fun (isom-from (suc n)
              ((snd (fst s-r) (fst r)) , (snd s-r) ∘ ( fst r ,_))) (snd r )

    in ((fst r) , fs) , se
  Iso.inv (isom-from (suc (suc n)) s) ((_ , _) , b) =
    _ , Iso.inv (isom-from (suc n) (_ , snd s ∘ (_ ,_))) (_ , b)
  Iso.rightInv (isom-from (suc (suc n)) s) ((a , r) , b) i =
    let z = Iso.rightInv (isom-from (suc n) (snd (fst s) a , snd s ∘ (a ,_)))
                 (r , b) i
    in (a , fst z) , snd z
  Iso.leftInv (isom-from (suc (suc n)) s) (_ , r) =
    cong (_ ,_) (Iso.leftInv (isom-from (suc n) _ ) r)
