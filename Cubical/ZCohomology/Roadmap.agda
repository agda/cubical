{-# OPTIONS --cubical #-}
module Cubical.ZCohomology.Roadmap where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_ ; 1+_ to 1+₋₂_)
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.HITs.Pushout

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

postulate
 Kn≡ΩKn+1 : (n : ℕ) → coHomK n ≡ typ (Ω (coHomK-ptd (suc n)))



0* : {n : ℕ} → coHomK n
0* {zero} = pt (coHomK-ptd zero)
0* {suc n} = pt (coHomK-ptd (suc n))



postulate
    _+̂'_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
    -̂' : {n : ℕ} → coHomK n → coHomK n
    +̂'rUnit : {n : ℕ} (x : coHomK n) → x +̂' 0* ≡ x
    +̂'lUnit : {n : ℕ} (x : coHomK n) → 0* +̂' x ≡ x
    +̂'rinv : {n : ℕ} (x : coHomK n) → x +̂' (-̂' x) ≡ 0*
    +̂'linv : {n : ℕ} (x : coHomK n) → (-̂' x) +̂' x ≡ 0*
    +̂'assoc : {n : ℕ} (x y z : coHomK n) → (x +̂' y) +̂' z ≡ x +̂' (y +̂' z)
    +̂'comm : {n : ℕ} (x y : coHomK n) → x +̂' y ≡ y +̂' x


_+̂_ : {n : ℕ} → coHom n A  → coHom n A → coHom n A
_+̂_ {A = A} {n = n}  = elimSetTrunc2 {B = λ _ _ → coHom n A}
                                     (λ _ _ → setTruncIsSet )
                                     λ a b → ∣ (λ x → (a x) +̂' (b x)) ∣₀

-̂_ : {n : ℕ} → coHom n A  → coHom n A
-̂_ {A = A} {n = n} = elimSetTrunc {B = λ _ → coHom n A} (λ _ → setTruncIsSet) λ a → ∣ (λ x → -̂' (a x)) ∣₀ 

0̂ : {n : ℕ} → coHom n A
0̂ {n = n} = ∣ (λ _ → 0*) ∣₀

_* :  {n : ℕ} (f : B → A) → coHom n A  → coHom n B
_* {B = B} {A = A} {n = n} f = elimSetTrunc {B = λ _ → coHom n B}
                                            (λ _ → setTruncIsSet)
                                            λ β → ∣ (λ x → (β (f x))) ∣₀

_*-Red :  {n : ℕ} {A : Pointed ℓ} {B : Pointed ℓ'} (f : B →* A) → coHomRed n A  → coHomRed n B
_*-Red {n = n}  {A = A} {B = B}  f = elimSetTrunc {B = λ _ → coHomRed n B}
                                            (λ _ → setTruncIsSet)
                                            λ β → ∣ (λ x → fst β (fst f x)) , (λ i → (fst β (snd f i))) ∙ snd β ∣₀



module Mayer-Vietoris where
  inj : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         coHomRed n ((Pushout f g) , inl (pt A)) → coHomRed n A × coHom n B
  inj {A = A} {B = B} {C = C} {n = zero} {f = f} {g = g} = elimSetTrunc (λ _ → hLevelProd (suc (suc zero)) setTruncIsSet setTruncIsSet) λ d → ((_*-Red) {n = zero} inl' ) ∣ d ∣₀ ,  (inr *) ∣ fst d ∣₀  
    module MV-help where
      inl' : A →* ((Pushout f g) , inl (pt A))
      inl' = inl , refl
  inj {A = A} {B = B} {C = C} {n = suc n} {f = f} {g = g} = elimSetTrunc (λ _ → hLevelProd (suc (suc zero)) setTruncIsSet setTruncIsSet) λ d → ((_*-Red) {n = (suc n)} MV-help.inl' ) ∣ d ∣₀ ,  (inr *) ∣ fst d ∣₀

  Δfun : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         (coHomRed n A) × (coHom n B) →  coHom n C
  Δfun {A = A} {B = B} {n = zero} {f = f} {g = g} (a , b) = elimSetTrunc (λ _ → setTruncIsSet) (λ d → (f *) ∣ fst d ∣₀) a
                                                                    +̂
                                                                    (-̂ elimSetTrunc (λ _ → setTruncIsSet) (λ d → (g *) ∣ d ∣₀) b) 
  Δfun {A = A} {B = B} {n = suc n} {f = f} {g = g} (a , b) = elimSetTrunc (λ _ → setTruncIsSet) (λ d → (f *) ∣ fst d ∣₀) a
                                                                    +̂
                                                                    (-̂ elimSetTrunc (λ _ → setTruncIsSet) (λ d → (g *) ∣ d ∣₀) b)

  d-fun : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         coHom n C → coHomRed n (Pushout f g , inl (pt A))
  d-fun {A = A} {B = B} {C = C} {n = n} {f = f} {g = g}  = elimSetTrunc (λ _ → setTruncIsSet) λ γ → ∣ {!(d̃-fun γ)!} ∣₀ where -- need to pattern match on n
    more : (Pushout f g , inl (pt A)) →* coHomK-ptd n
    more = (λ x → {!!}) , {!!} where
      more+ : (Pushout f g) → (coHomK n)
      more+ = {!!}
    d̃-fun : (C → (coHomK n)) → typ ((Pushout f g , inl (pt A)) →* coHomK-ptd (suc n) *)
    d̃-fun fun = d̃' , refl
      where
      d̃' : Pushout f g → ∥ S₊ (suc n) ∥ suc (ℕ→ℕ₋₂ n)
      d̃' (inl x) = 0*
      d̃' (inr x) = 0*
      d̃' (push a i) = (transport (λ i → Kn≡ΩKn+1 n i) (fun a)) i
