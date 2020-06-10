{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Sigma.Record.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Equiv.Fiberwise

open import Cubical.Data.List renaming (_++_ to _++L_)
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)
open import Cubical.HITs.Interval.NCube




Sig : ∀ ℓ → ℕ →  Type (ℓ-suc ℓ)
Sig ℓ zero = Lift Unit
Sig ℓ (suc zero) = Type ℓ
Sig ℓ (suc (suc n)) = Σ (Type ℓ) λ x → x → Sig ℓ (suc n)

Rec : ∀ {ℓ} → ∀ n → Sig ℓ n → Type ℓ
Rec zero _ = Lift Unit
Rec (suc zero) Ty = Ty
Rec (suc (suc n)) (Ty , →Sig) = Σ Ty (Rec (suc n)∘ →Sig)


prependTy : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → (A → Sig ℓ n) → Sig ℓ (suc n)
prependTy {n = zero} {A} _ = A
prependTy {n = suc n} = _ ,_ 

prependVal : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)
                → (x : A)
                → Rec n (s x)
                → Rec (suc n) (prependTy {n = n} s)
prependVal {n = zero} s x _ = x
prependVal {n = suc n} s = _,_


Sig-section-from : ∀ {ℓ} → ∀ {n m}
           → (sₙ : Sig ℓ n)
           → (sₘ : Rec n sₙ →  Sig ℓ m)
           → Sig ℓ (n + m)
Sig-section-from {n = zero} sₙ sₘ = sₘ _
Sig-section-from {n = suc zero} {m} sₙ sₘ = prependTy {n = m} {A = sₙ} sₘ
Sig-section-from {n = suc (suc n)} {m} sₙ sₘ =
   prependTy {n = (suc n) + m}
     λ x → Sig-section-from {n = suc n} {m} (snd sₙ x) (sₘ ∘ (x ,_)) 

Sig-section-to : ∀ {ℓ} → ∀ {n m}
           → Sig ℓ (n + m)
           → Σ[ sₙ ∈  Sig ℓ n ] (Rec n sₙ → Sig ℓ m)
Sig-section-to {n = zero} x = _ , const x
Sig-section-to {n = suc zero} {zero} = _, _
Sig-section-to {n = suc zero} {suc m} = idfun _
Sig-section-to {n = suc (suc n)} x =
  let z = λ (y : fst x) → Sig-section-to {n = suc n} (snd x y)
  in (fst x , fst ∘ z) ,  uncurry (snd ∘ z)

Sig-section-to-from : ∀ {ℓ} → ∀ {n m}
    → section (Sig-section-to {ℓ} {n} {m}) (uncurry (Sig-section-from {ℓ} {n} {m}))
Sig-section-to-from {n = zero} b = refl
Sig-section-to-from {n = suc zero} {zero} b = refl
Sig-section-to-from {n = suc zero} {suc m} b = refl
Sig-section-to-from {n = suc (suc n)} {m} b i =
  let z = λ (y : fst (fst b)) →
            Sig-section-to-from {n = (suc n)} {m = m} (snd (fst b) y , snd b ∘ (y ,_)) i
  in ((fst (fst b)) ,  fst ∘ z) , uncurry (snd ∘ z)

Sig-section-from-to : ∀ {ℓ} → ∀ {n m}
    → retract (Sig-section-to {ℓ} {n} {m}) (uncurry (Sig-section-from {ℓ} {n} {m}))
Sig-section-from-to {n = zero} a = refl
Sig-section-from-to {n = suc zero} {zero} a = refl
Sig-section-from-to {n = suc zero} {suc m} a = refl
Sig-section-from-to {n = suc (suc n)} {m} a i =
  prependTy {n = (suc n) + m} λ (y : fst a) → Sig-section-from-to {n = suc n} {m} (snd a y) i

Sig-section-Iso : ∀ {ℓ} → ∀ {n m}
                   → Iso (Sig ℓ (n + m))
                         (Σ[ sₙ ∈  Sig ℓ n ] (Rec n sₙ → Sig ℓ m))
Sig-section-Iso {ℓ} {n} {m} =
  iso (Sig-section-to {n = n} {m}) (uncurry (Sig-section-from {n = n} {m}))
      (Sig-section-to-from {ℓ} {n} {m}) (Sig-section-from-to {ℓ} {n} {m})


Rec-section-to :  ∀ {ℓ} → ∀ {n m} 
                       → (s : Sig ℓ (n + m))
                       → Rec (n + m) s
                       → Σ (Rec n (fst (Sig-section-to {n = n} s)))
                           (Rec m ∘ (snd (Sig-section-to {n = n} {m = m} s))) 
Rec-section-to {n = zero} s x = _ , x
Rec-section-to {n = suc zero} {zero} s = _, _
Rec-section-to {n = suc zero} {suc m} s x = x
Rec-section-to {n = suc (suc n)} {m} s x =
   _ , snd (Rec-section-to {n = suc n} ((snd s) (fst x)) (snd x))

Rec-section-from :  ∀ {ℓ} → ∀ {n m} 
                       → (sₙ : Sig ℓ n)
                       → (sₘ : Rec n sₙ →  Sig ℓ m)
                       → Σ (Rec n sₙ)
                           (Rec m ∘ sₘ)
                       → Rec (n + m) (Sig-section-from {n = n} {m = m}  sₙ sₘ)
Rec-section-from {n = zero} sₙ sₘ = snd
Rec-section-from {n = suc zero} {m} sₙ sₘ = prependVal {n = m} {A = sₙ} sₘ _ ∘ snd
Rec-section-from {n = suc (suc n)} {m} sₙ sₘ x =
     prependVal {n = suc n + m} (_) _
      (Rec-section-from {n = suc n} _ _ (_ , snd x))

-- Rec-section-iso : ∀ {ℓ} → ∀ {n m} 
--                        → (s : Sig ℓ (n + m))
--                        → Iso (Rec {n = n + m} s)
--                          (Σ (Rec {n = n} (fst (Sig-section-to {n = n} s)))
--                            (Rec {n = m} ∘ (snd (Sig-section-to {n = n} {m = m} s)))) 
-- Rec-section-iso s = {!!}



-- this split could be done with sections, but would introduce transp during conversion 
-- betwen Sig (1 + n) and Sig (n + 1) 

Sig-n+1-split : ∀ {ℓ} → ∀ n → Sig ℓ (suc n) → Σ (Sig ℓ n) (λ sₙ → Rec n sₙ → Sig ℓ 1)
Sig-n+1-split zero s =  _ , const s
Sig-n+1-split 1 s = s
Sig-n+1-split (suc (suc n)) s =
  let z : (fst s) → _
      z x = Sig-n+1-split (suc n) (snd s x)

  in (fst s , fst ∘ z ) , uncurry (snd ∘ z)

Sig-n+1-unsplit : ∀ {ℓ} → ∀ n → Σ (Sig ℓ n) (λ sₙ → Rec n sₙ → Sig ℓ 1) → Sig ℓ (suc n) 
Sig-n+1-unsplit zero x = snd x _
Sig-n+1-unsplit (suc zero) x = x
Sig-n+1-unsplit (suc (suc n)) (s , r→Ty) =
  (fst s) , λ x → Sig-n+1-unsplit (suc n) ((snd s) x , r→Ty ∘ (x ,_))

Sig-n+1-iso : ∀ {ℓ} → ∀ n → Iso (Σ (Sig ℓ n) (λ sₙ → Rec n sₙ → Sig ℓ 1)) (Sig ℓ (suc n)) 
Iso.fun (Sig-n+1-iso n) = Sig-n+1-unsplit n
Iso.inv (Sig-n+1-iso n) = Sig-n+1-split n
Iso.rightInv (Sig-n+1-iso zero) b = refl
Iso.rightInv (Sig-n+1-iso (suc zero)) b = refl
Iso.rightInv (Sig-n+1-iso (suc (suc n))) (s , z) =
  cong ( s ,_ ) (funExt λ x → Iso.rightInv (Sig-n+1-iso (suc n)) (z x))

Iso.leftInv (Sig-n+1-iso zero) a = refl
Iso.leftInv (Sig-n+1-iso (suc zero)) a = refl
Iso.leftInv (Sig-n+1-iso (suc (suc n))) ((Ty , s) , r→Ty) i =
  let z : Ty → _
      z x = (Iso.leftInv (Sig-n+1-iso (suc n))) (s x , (r→Ty ∘ (x ,_))) i

  in (Ty , fst ∘ z) , uncurry (snd ∘ z)

Rec-n+1-split-iso : ∀ {ℓ} → ∀ n → (s : Sig ℓ (suc n)) →
                        Iso (Rec (suc n) s) (Σ _ (snd (Sig-n+1-split n s)))
Rec-n+1-split-iso zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
Rec-n+1-split-iso 1 s = idIso
Rec-n+1-split-iso {ℓ} (suc (suc n)) s =
 let prev = Rec-n+1-split-iso {ℓ} (suc n) in 
 iso (λ r → let (fs , se) = Iso.fun (prev ((snd s) (fst r))) (snd r)
            in (fst r , fs) , se )
     (λ r → fst (fst r) , Iso.inv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r))
     (λ r i → let (fs , se) = Iso.rightInv (prev ((snd s) (fst (fst r)))) (snd (fst r) , snd r) i
              in (fst (fst r) , fs) , se)
     λ r i →   let (fs , se) =
                     Iso.leftInv (prev ((snd s) (fst r))) (snd r) i
               in (fst r) , fs , se

Rec-n+1-unsplit-iso : ∀ {ℓ} → ∀ n →
                         (s-r  : Σ (Sig ℓ n) λ z → Rec n z → Sig ℓ 1) →
                          Iso (Rec (suc n) (Sig-n+1-unsplit {ℓ} n s-r)) (Σ _ (snd s-r))
Rec-n+1-unsplit-iso zero s = iso (_ ,_) snd (λ b → refl) λ a → refl
Rec-n+1-unsplit-iso 1 s = idIso
Iso.fun (Rec-n+1-unsplit-iso (suc (suc n)) s-r) r =
  let (fs , se) = Iso.fun (Rec-n+1-unsplit-iso (suc n)
            ((snd (fst s-r) (fst r)) , (snd s-r) ∘ ( fst r ,_))) (snd r )

  in ((fst r) , fs) , se
Iso.inv (Rec-n+1-unsplit-iso (suc (suc n)) s) ((_ , _) , b) =
  _ , Iso.inv (Rec-n+1-unsplit-iso (suc n) (_ , snd s ∘ (_ ,_))) (_ , b)
Iso.rightInv (Rec-n+1-unsplit-iso (suc (suc n)) s) ((a , r) , b) i =
  let z = Iso.rightInv (Rec-n+1-unsplit-iso (suc n) (snd (fst s) a , snd s ∘ (a ,_)))
               (r , b) i
  in (a , fst z) , snd z
Iso.leftInv (Rec-n+1-unsplit-iso (suc (suc n)) s) (_ , r) =
  cong (_ ,_) (Iso.leftInv (Rec-n+1-unsplit-iso (suc n) _ ) r)
 

-- generating function and types

iso-Π-Π' : ∀ {ℓ ℓ'} {A : Type ℓ}
               → (B : A → Type ℓ')
               → Iso (Π B) (Π' B)
iso-Π-Π' B = iso (λ x {y} → x y) (λ x y → x {y}) (λ b → refl) (λ b → refl)


λ' : ∀ {ℓ ℓ'} (A : Type ℓ)
               → (B : A → Type ℓ')
               → Π B → ∀ i → isoToPath (iso-Π-Π' B) i
λ' A B x i = coe0→i (λ i → isoToPath (iso-Π-Π' B) i) i x

app' : ∀ {ℓ ℓ'} (A : Type ℓ)
               → (B : A → Type ℓ')
               → ∀ i → isoToPath (iso-Π-Π' B) i → Π B
app' A B i x = coei→0 (λ i → isoToPath (iso-Π-Π' B) i) i x


-- generates a type of maximaly uncurried functions from record of given sginature

fromSigType : ∀ {ℓ} → ∀ n → NCube n → Sig ℓ n → Type ℓ → Type ℓ 
fromSigType zero _ _ Target = Target
fromSigType (suc zero) v s Target =
    I-rec (isoToPath (iso-Π-Π' {A = s} λ x₂ → Target)) (head v) 
fromSigType (suc (suc n)) v s Target =
   I-rec (isoToPath
    (iso-Π-Π' {A = fst s} λ x → fromSigType (suc n) (tail v) (snd s x) Target))
      (head v)

-- version for higher level
fromSigType-Ty : ∀ {ℓ} → ∀ n → NCube n → Sig ℓ n → Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ) 
fromSigType-Ty zero _ _ Target = Target
fromSigType-Ty (suc zero) v s Target =
    I-rec (isoToPath (iso-Π-Π' {A = s} λ x₂ → Target)) (head v) 
fromSigType-Ty (suc (suc n)) v s Target =
   I-rec (isoToPath
    (iso-Π-Π' {A = fst s} λ x → fromSigType-Ty (suc n) (tail v) (snd s x) Target))
      (head v)




mkFun : ∀ {ℓ} → ∀ n → (v : Vec Interval n) → (s : Sig ℓ n) → (Target : Type ℓ)
           → (Rec n s → Target)
           → fromSigType n v s Target
mkFun zero v s Target x = x _
mkFun (suc zero) (i' ∷ _) s Target x =
  I-elim (I-rec (isoToPath (iso-Π-Π' λ _ → Target))) (λ i → λ' s (λ z → Target) x i ) i'
mkFun (suc (suc n)) v s Target x =
  I-elim (I-rec (isoToPath (iso-Π-Π' _))) (λ i → λ' _ _
    (λ x₁ → mkFun (suc n) (tail v) (snd s x₁) Target λ x₂ → x (x₁ , x₂))
    i ) (head v)

mkFun-Ty : ∀ {ℓ} → ∀ n → (v : Vec Interval n) → (s : Sig ℓ n) → (Target : Type (ℓ-suc ℓ))
           → (Rec n s → Target)
           → fromSigType-Ty n v s Target
mkFun-Ty zero v s Target x = x _
mkFun-Ty (suc zero) v s Target x =
  I-elim (I-rec (isoToPath (iso-Π-Π' {A = s} λ _ → Target))) (λ i → λ' s (λ z → Target) x i )
     (head v)
mkFun-Ty (suc (suc n)) v s Target x =
  I-elim (I-rec (isoToPath (iso-Π-Π' _))) (λ i → λ' _ _
    (λ x₁ → mkFun-Ty (suc n) (tail v) (snd s x₁) Target λ x₂ → x (x₁ , x₂))
    i ) (head v)

from-mkFun-Ty : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → (Target : Type (ℓ-suc ℓ))          
           → fromSigType-Ty n (corner0) s Target
           → (Rec n s → Target)
from-mkFun-Ty zero s Target x _ = x
from-mkFun-Ty {ℓ} (suc zero) s Target x = x
from-mkFun-Ty (suc (suc zero)) s Target = uncurry
from-mkFun-Ty (suc (suc (suc n))) s Target x =
  uncurry λ x₁ →  from-mkFun-Ty (suc (suc n)) (snd s x₁) Target (x x₁)

constructorType : ∀ {ℓ} → ∀ n → Vec Interval n → Sig ℓ n → Type ℓ 
constructorType n v s = fromSigType n v s (Rec n s)

mkConstructor : ∀ {ℓ} → ∀ n → (v : Vec Interval n) → (s : Sig ℓ n)
                  → constructorType n v s
mkConstructor n v s = mkFun n v s (Rec n s) (idfun _) 

-- dependnt functions

fromSigType-dep : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → (Rec n s → Type ℓ) → Type ℓ 
fromSigType-dep zero s x = x _
fromSigType-dep (suc zero) s x = Π x
fromSigType-dep (suc (suc n)) s x =
  Π λ x₁ → fromSigType-dep (suc n) (snd s x₁) (x ∘ (x₁ ,_))

mk-fromSigType-dep : ∀ {ℓ} → ∀ n → (s : Sig ℓ n)
                     → (A : Rec n s → Type ℓ)
                     → Π A → fromSigType-dep n s A
mk-fromSigType-dep zero s A x = x _
mk-fromSigType-dep (suc zero) s A = idfun _
mk-fromSigType-dep (suc (suc n)) s A f x =
  mk-fromSigType-dep (suc n) (snd s x) (A ∘ (x ,_)) (f ∘ (x ,_))


fromSigType-dep-Lower : ∀ {ℓ} → ∀ n → (s : Sig (ℓ-suc ℓ) n) → (Rec n s → Type ℓ) → Type (ℓ-suc ℓ) 
fromSigType-dep-Lower zero s x = Lift (x _)
fromSigType-dep-Lower (suc zero) s x = Π x
fromSigType-dep-Lower (suc (suc n)) s x =
  Π λ x₁ → fromSigType-dep-Lower (suc n) (snd s x₁) (x ∘ (x₁ ,_))

mk-fromSigType-dep-Lower : ∀ {ℓ} → ∀ n → (s : Sig (ℓ-suc ℓ) n)
                     → (A : Rec n s → Type ℓ)
                     → Π A → fromSigType-dep-Lower n s A
mk-fromSigType-dep-Lower zero s A x = lift (x _)
mk-fromSigType-dep-Lower (suc zero) s A = idfun _
mk-fromSigType-dep-Lower (suc (suc n)) s A f x =
  mk-fromSigType-dep-Lower (suc n) (snd s x) (A ∘ (x ,_)) (f ∘ (x ,_)) 

-- records of shape described by List of Bools

Recc : ∀ {ℓ} → ∀ n → (v : List Bool) → (s : Sig ℓ (suc (suc (suc n)))) → Type ℓ

Recc-≃ : ∀ {ℓ} → ∀ n → (v : List Bool) → (s : Sig ℓ (suc (suc (suc n)))) →
                        Recc n v s ≃ Rec (3 + n) s  


Recc n [] =  Rec (3 + n)
Recc zero (false ∷ v) s = Rec 3 s
Recc (suc n) (false ∷ v) s = Σ (fst s) ( Recc n v ∘ snd s)
Recc zero (true ∷ v) s = Σ (Σ (fst s) (fst ∘ snd s)) λ x → snd (snd s (fst x)) (snd x)
Recc (suc n) (true ∷ v) s =
  let (s- , r→s) = Sig-n+1-split (3 + n) s
  in  Σ (Recc n v s-) (r→s ∘ fst (Recc-≃ n v s-))

replic : ∀ {ℓ} → {A : Type ℓ} → ℕ → A → List A
replic zero _ = []
replic (suc x) a = a ∷ replic x a

mapConst : ∀ {ℓ} → {A : Type ℓ} → List A → A → List A
mapConst [] _ = []
mapConst (x ∷ x₁) a = a ∷ mapConst x₁ a


ReccF-≃ : ∀ {ℓ} → ∀ n → (v : List Bool) → (s : Sig ℓ (suc (suc (suc n)))) →
                        Recc n (mapConst v false) s ≃ Rec (3 + n) s  
ReccF-≃ n [] s = idEquiv _
ReccF-≃ zero (x ∷ v) s = idEquiv _
ReccF-≃ (suc n) (x ∷ v) s =
 Σ-cong-equiv-snd λ a → ReccF-≃ n v (snd s a)

Recc-v-≃ : ∀ {ℓ} → ∀ n → (v : List Bool) → (s : Sig ℓ (suc (suc (suc n)))) →
                        Recc n v s ≃
                          Recc n (mapConst v false) s
Recc-v-≃ n [] s = idEquiv _
Recc-v-≃ zero (false ∷ v) s = idEquiv _
Recc-v-≃ (suc n) (false ∷ v) s =
  Σ-cong-equiv-snd λ a → Recc-v-≃ n v (snd s a)
Recc-v-≃ zero (true ∷ v) s = Σ-assoc-≃
Recc-v-≃ {ℓ} (suc n) (true ∷ v) s =
  let (s- , r→s) = Sig-n+1-split (3 + n) s
  in  
  compEquiv (Σ-cong-equiv-fst {ℓ} {B = r→s} (Recc-≃ n v s-))
  (compEquiv (invEquiv (isoToEquiv (Rec-n+1-split-iso (3 + n) s)))
   (invEquiv (ReccF-≃ (suc n) (true ∷ v) s )))

Recc-≃ n v s = compEquiv (Recc-v-≃ n v s) (ReccF-≃ n v s)

-- records of "rigth-most" shape

Recᵣ : ∀ {ℓ} → ∀ n → (Sig ℓ n) → Type ℓ
Recᵣ zero = const (Lift Unit)
Recᵣ (suc zero) = idfun _
Recᵣ (suc (suc zero)) = (uncurry Σ)
Recᵣ (suc (suc (suc n))) = Recc n (replic (suc n) true)

-- this is analogue to Σ-assoc, but is acting on all levels at once

Recᵣ≃ : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → Recᵣ n s ≃ Rec n s 
Recᵣ≃ zero s = idEquiv _
Recᵣ≃ (suc zero) s = idEquiv _
Recᵣ≃ (suc (suc zero)) s = idEquiv _
Recᵣ≃ (suc (suc (suc n))) s = Recc-≃ n (replic (suc n) true) s


SigR : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)

SigR≃S : ∀ {ℓ} → ∀ n → (SigR ℓ n) ≃ (Sig ℓ n)

SigR ℓ 0 = Sig ℓ 0
SigR ℓ 1 = Sig ℓ 1
SigR ℓ 2 = Sig ℓ 2
SigR ℓ (suc (suc (suc n))) =
  Σ (SigR ℓ (suc (suc n))) (λ x →
    (Recᵣ (suc (suc n)) ∘ equivFun (SigR≃S (suc (suc n)))) x → Type _ )


SigR≃S 0 = idEquiv _
SigR≃S 1 = idEquiv _
SigR≃S 2 = idEquiv _

SigR≃S {ℓ} (suc (suc (suc n))) =
   compEquiv ((Σ-cong-equiv-fst {A = SigR ℓ (suc (suc n))}
        {B = λ a → (Recᵣ (suc (suc n))) a → Type ℓ} ((SigR≃S (suc (suc n))))))
   (compEquiv ( (Σ-cong-equiv-snd λ a → cong≃ (λ x → x → Type ℓ)  (Recᵣ≃ ( 2 + n) _)))
                (isoToEquiv (Sig-n+1-iso (suc (suc n)))))


-- we can construct "signature of signatures"
-- encoding signatures into records of higher level

SSig : ∀ ℓ → ∀ n → (Sig (ℓ-suc ℓ) n)

SSig→ : ∀ {ℓ} → ∀ n → Rec n (SSig ℓ n) → Sig ℓ n

SSig ℓ zero = _
SSig ℓ (suc zero) = Type _
SSig ℓ (suc (suc n)) =
 Sig-n+1-unsplit (suc n) ((SSig ℓ (suc n)) ,
  (λ x → fromSigType-Ty (suc n) corner0 x (Type ℓ) ) ∘ SSig→ (suc n))


SSig→ zero x = x
SSig→ (suc zero) x = x
SSig→ (suc (suc zero)) x = x
SSig→ (suc (suc (suc n))) x =
  let (_ , y) = Iso.fun (Rec-n+1-unsplit-iso (suc (suc  n)) (SSig _ _ ,
         (λ x₁ → fromSigType-Ty (suc (suc  n)) corner0 x₁ _ ) ∘ SSig→ _)) x  
  in Sig-n+1-unsplit _
            ((SSig→ _ _) ,
                from-mkFun-Ty (suc (suc  n)) _ (Type _) y)

-- SSig← : ∀ {ℓ} → ∀ n → Sig ℓ n → Rec n (SSig ℓ n)
-- SSig← zero x = x
-- SSig← (suc zero) x = x
-- SSig← (suc (suc zero)) x = x
-- SSig← (suc (suc (suc n))) x =
--   let z = {!!}

--   in {!!}

mk-Σ-assoc-n : ∀ {ℓ} → ∀ n → _
mk-Σ-assoc-n {ℓ} n =
  mk-fromSigType-dep-Lower n (SSig ℓ n)
   ((λ x →  Recᵣ n x ≃ Rec n x) ∘ SSig→ n)
     (Recᵣ≃ n ∘ SSig→ n)

