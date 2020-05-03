{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.MayerVietoris where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Group.Base

open import Cubical.ZCohomology.cupProdPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)
{-
record AbGroup {ℓ} (A : Type ℓ) : Type ℓ where
  constructor abgr
  field
    noll : A
    _⊕_ : A → A → A
    associate : (a b c : A) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    commute : (a b : A) → a ⊕ b ≡ (b ⊕ a)
    r-unit : (a : A) → a ⊕ noll ≡ a
    negate : (a : A) → Σ[ a⁻ ∈ A ] (a ⊕ a⁻ ≡ noll)
-}
{-
grHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B)
     → AbGroup A → AbGroup B → Type (ℓ-max ℓ ℓ') 
grHom {A = A} {B = B} ϕ (abgr 0A _+A_ as-A comm-A r-A neg-A) (abgr 0B _+B_ as-B comm-B r-B neg-B) = (x y : A) → ϕ (x +A y) ≡ (ϕ x +B ϕ y)

ImHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B) (A' : AbGroup A) (B' : AbGroup B)
        →  grHom ϕ A' B' → Type (ℓ-max ℓ ℓ')
ImHom {A = A} {B = B} ϕ Agr Bgr hom = Σ[ b ∈ B ] Σ[ a ∈ A ] ϕ a ≡ b

KerHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B) (A' : AbGroup A) (B' : AbGroup B)
        →  grHom ϕ A' B' → Type (ℓ-max ℓ ℓ')
KerHom {A = A} {B = B} ϕ Agr (abgr 0B _+B_ as-B comm-B r-B neg-B) hom = Σ[ a ∈ A ] ϕ a ≡ 0B
-}


---


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''
    A' : Pointed ℓ
    B' : Pointed ℓ'


coHomFun : (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec setTruncIsSet λ β → ∣ β ∘ f ∣₀

coHomFun∙ : (n : ℕ) (f : A' →∙ B') → coHomRed n B' → coHomRed n A'
coHomFun∙ n (f , fpt) = sRec setTruncIsSet λ { (β , βpt) → ∣ β ∘ f , (λ i → β (fpt i)) ∙ βpt ∣₀}

coHomFun∙2 : (n : ℕ) (f : A → B' .fst) → coHomRed n B' → coHom n A
coHomFun∙2 zero f = sRec setTruncIsSet λ { (β , βpt) → ∣ β ∘ f ∣₀}
coHomFun∙2 (suc n) f = sRec setTruncIsSet λ { (β , βpt) → ∣ β ∘ f ∣₀}

module MV {ℓ ℓ' ℓ''} ((A , a₀) : Pointed ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  D : Pointed (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  D = Pushout f g , inl a₀

  -- σ : typ A → typ (Ω (∙Susp (typ A)))
  -- σ a = merid a ∙ merid (pt A) ⁻¹

  i : (n : ℕ) → coHomRed n D → coHomRed n (A , a₀) × coHom n B
  i zero = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                λ { (δ , δpt) →  ∣ (λ x → δ (inl x)) , δpt ∣₀ , ∣ (λ x → δ (inr x)) ∣₀ }
  i (suc n) = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                   λ { (δ , δpt) → ∣ (λ x → δ (inl x)) , δpt ∣₀ , ∣ (λ x → δ (inr x)) ∣₀ }

  Δ : (n : ℕ) → coHomRed n (A , a₀) × coHom n B → coHom n C
  Δ n (α , β) = coHomFun∙2 n f α +ₕ (-ₕ (coHomFun n g β))

  --
  
  d-pre1 : (n : ℕ) → (C → coHomK n) → D .fst → coHomK-ptd (suc n) .fst
  d-pre1 zero γ (inl x) = 0ₖ
  d-pre1 zero γ (inr x) = 0ₖ
  d-pre1 zero γ (push a i) = Kn→ΩKn+1 zero (γ a) i 
  d-pre1 (suc n) γ (inl x) = 0ₖ
  d-pre1 (suc n) γ (inr x) = 0ₖ
  d-pre1 (suc n) γ (push a i) = Kn→ΩKn+1 (suc n) (γ a) i

  d-pre1∙ : (n : ℕ) → (γ : (C → coHomK n)) → d-pre1 n γ (snd D) ≡ ∣ north ∣
  d-pre1∙ zero γ = refl
  d-pre1∙ (suc n) γ = refl

  d-pre2 : (n : ℕ) → (C → coHomK n) → D →∙ coHomK-ptd (suc n)
  d-pre2 n γ = d-pre1 n γ , d-pre1∙ n γ

  d : (n : ℕ) → coHom n C → coHomRed (suc n) D
  d n = sRec setTruncIsSet λ a → ∣ d-pre2 n a ∣₀

  iIsHom : (n : ℕ) (x y : coHomRed n D) → i n (+ₕ∙ n x y) ≡ +prod n (i n x) (i n y)
  iIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                    λ { (f , fpt) (g , gpt) → refl}
  iIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                    λ { (f , fpt) (g , gpt) → refl}

  prodElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : ∥ A ∥₀ × ∥ B ∥₀ → Type ℓ''}
          → ((x : ∥ A ∥₀ × ∥ B ∥₀) → isOfHLevel 2 (C x))
          → ((a : A) (b : B) → C (∣ a ∣₀ , ∣ b ∣₀))
          → (x : ∥ A ∥₀ × ∥ B ∥₀) → C x
  prodElim {A = A} {B = B} {C = C} hlevel ind (a , b) = schonf a b
    where
    schonf : (a : ∥ A ∥₀) (b : ∥ B ∥₀) → C (a , b)
    schonf = sElim (λ x → isOfHLevelΠ 2 λ y → hlevel (_ , _)) λ a → sElim (λ x → hlevel (_ , _))
                   λ b → ind a b

  ΔIsHom : (n : ℕ) (x y : coHomRed n (A , a₀) × coHom n B) → Δ n (+prod n x y) ≡ (Δ n x +ₕ Δ n y)
  ΔIsHom zero = prodElim (λ x → isOfHLevelΠ 2 λ y → isOfHLevelPath 2 setTruncIsSet _ _ )
                         λ {(f' , fpt) x1 → prodElim (λ x → isOfHLevelPath 2 setTruncIsSet _ _)
                           λ {(g' , gpt) x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)}}
  ΔIsHom (suc n) = prodElim (λ x → isOfHLevelΠ 2 λ y → isOfHLevelPath 2 setTruncIsSet _ _ )
                         λ {(f' , fpt) x1 → prodElim (λ x → isOfHLevelPath 2 setTruncIsSet _ _)
                           λ {(g' , gpt) x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                               (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)}}

  helper : (h l : C → Int) (x : D .fst) → (d-pre1 zero h x +ₖ d-pre1 zero l x) ≡ d-pre1 zero (λ x → h x +ₖ l x) x
  helper h l (inl x) = lUnitₖ 0ₖ
  helper h l (inr x) = lUnitₖ 0ₖ
  helper h l (push a i) = hcomp {!!} (cong (λ x → x i) helper1)
    where
    helper1 : cong₂ (λ x y → x +ₖ y) (Kn→ΩKn+1 zero (h a)) (Kn→ΩKn+1 zero (l a)) ≡ Kn→ΩKn+1 zero (h a +ₖ l a)
    helper1 = {!!}

    pp : PathP (λ i → lUnitₖ (0ₖ {n = 1}) i ≡ lUnitₖ 0ₖ i) (λ i → Kn→ΩKn+1 zero (h a) i +ₖ Kn→ΩKn+1 zero (l a) i) (Kn→ΩKn+1 zero (h a +ₖ l a))
    pp = toPathP ((λ z → transport (λ i → lUnitₖ (0ₖ {n = 1}) i ≡ lUnitₖ 0ₖ i) (lUnit (rUnit (λ i → Kn→ΩKn+1 zero (h a) i +ₖ Kn→ΩKn+1 zero (l a) i) z) z ))
                ∙ (λ z → transp (λ i → lUnitₖ (0ₖ {n = 1}) (i ∨ z) ≡ lUnitₖ 0ₖ (i ∨ z)) z
                                 (((λ i → lUnitₖ (0ₖ {n = 1}) ((~ i) ∧ z)) ∙ (λ i → Kn→ΩKn+1 zero (h a) i +ₖ Kn→ΩKn+1 zero (l a) i)
                               ∙ λ i → lUnitₖ (0ₖ {n = 1}) (i ∧ z))))
                ∙ (λ z → sym ((λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ 1 i ∙ Kn→ΩKn+1 1 0ₖ)) ∙
                       (λ i → ΩKn+1→Kn (lUnit (Kn→ΩKn+1 1 0ₖ) (~ i))) ∙
                       Iso.leftInv (Iso2-Kn-ΩKn+1 1) 0ₖ)
                  ∙ (lUnit (rUnit (λ i → Kn→ΩKn+1 zero (h a) i +ₖ Kn→ΩKn+1 zero (l a) i) z) z)
                  ∙ ((λ i → ΩKn+1→Kn (Kn→ΩKn+10ₖ 1 i ∙ Kn→ΩKn+1 1 0ₖ)) ∙
                       (λ i → ΩKn+1→Kn (lUnit (Kn→ΩKn+1 1 0ₖ) (~ i))) ∙
                       Iso.leftInv (Iso2-Kn-ΩKn+1 1) 0ₖ))
                ∙ (λ z → sym (lUnitₖ (0ₖ {n = 1}))
                       ∙ (lUnit (rUnit refl z ) z ∙ (λ i → ΩKn+1→Kn (Kn→ΩKn+1 1 (Kn→ΩKn+1 zero (h a) i) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 zero (l a) i))) ∙ lUnit (rUnit refl z) z)
                       ∙ lUnitₖ (0ₖ {n = 1}))
                ∙ ((λ z → sym (lUnitₖ (0ₖ {n = 1}))
                       ∙ (({!!} ∙ {!ΩKn+1→Kn (Kn→ΩKn+1 1 (Kn→ΩKn+1 zero (h a) i) ∙ Kn→ΩKn+1 1 (Kn→ΩKn+1 zero (l a) i)!} ∙ λ i → {!l!})
                       ∙ (λ i → Iso.leftInv (Iso2-Kn-ΩKn+1 1) {!!} {!!}) ∙ (λ i → (Iso.leftInv (Iso2-Kn-ΩKn+1 1) 0ₖ (~ i ∧ z))) ∙ {!!} ∙ {!!})
                       ∙ lUnitₖ (0ₖ {n = 1})))
                ∙ {!!}
                ∙ {!!}
                ∙ {!!}) -- compPathP (λ j i → {!!}) (compPathP {!!} (compPathP {!!} {!!}))

  dIsHom : (n : ℕ) (x y : coHom n C) → d n (x +ₕ y) ≡ +ₕ∙ (suc n) (d n x) (d n y)
  dIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                       λ h l → (λ i → ∣ (λ x → helper h l x (~ i)) , lUnit (λ j → lUnitₖ 0ₖ (j ∨ (~ i))) i ∣₀) ∙
                                (λ i → ∣ (λ x → d-pre1 zero h x +ₖ d-pre1 zero l x) , refl ∙ lUnitₖ 0ₖ ∣₀)
  dIsHom (suc n) = {!d-pre1 zero h x +ₖ d-pre1 zero l x!}

-- record LES {ℓ} (B : ℕ → Type ℓ) (0' : {n : ℕ} → B n) (f : {n : ℕ} → B n → B (suc n)) (_+'_ : {n : ℕ} → B n → B n → B n) : Type ℓ where
--   constructor les
--   field
--     grp : (n : ℕ) → AbGroup (B n) 0' _+'_
--     imIsKer : (n : ℕ) → {!!}
    

-- {-
-- record Ring {ℓ} (A : Type ℓ) (_+∙_ :) : Type (ℓ-max ℓ ℓ') where
--   constructor iso
--   field
--     fun : A → B
--     inv1 : B → A
--     rightInv : section fun inv1
--     leftInv : retract fun inv1
-- -}
