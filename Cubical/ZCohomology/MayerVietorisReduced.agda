
{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.MayerVietorisReduced where

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


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)


-- {-
-- record AbGroup {ℓ} (A : Type ℓ) : Type ℓ where
--   constructor abgr
--   field
--     noll : A
--     _⊕_ : A → A → A
--     associate : (a b c : A) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
--     commute : (a b : A) → a ⊕ b ≡ (b ⊕ a)
--     r-unit : (a : A) → a ⊕ noll ≡ a
--     negate : (a : A) → Σ[ a⁻ ∈ A ] (a ⊕ a⁻ ≡ noll)
-- -}
-- {-
-- grHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B)
--      → AbGroup A → AbGroup B → Type (ℓ-max ℓ ℓ') 
-- grHom {A = A} {B = B} ϕ (abgr 0A _+A_ as-A comm-A r-A neg-A) (abgr 0B _+B_ as-B comm-B r-B neg-B) = (x y : A) → ϕ (x +A y) ≡ (ϕ x +B ϕ y)
-- ImHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B) (A' : AbGroup A) (B' : AbGroup B)
--         →  grHom ϕ A' B' → Type (ℓ-max ℓ ℓ')
-- ImHom {A = A} {B = B} ϕ Agr Bgr hom = Σ[ b ∈ B ] Σ[ a ∈ A ] ϕ a ≡ b
-- KerHom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ϕ : A → B) (A' : AbGroup A) (B' : AbGroup B)
--         →  grHom ϕ A' B' → Type (ℓ-max ℓ ℓ')
-- KerHom {A = A} {B = B} ϕ Agr (abgr 0B _+B_ as-B comm-B r-B neg-B) hom = Σ[ a ∈ A ] ϕ a ≡ 0B
-- -}


-- ---


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

module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  D : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  D = Pushout f g

  -- σ : typ A → typ (Ω (∙Susp (typ A)))
  -- σ a = merid a ∙ merid (pt A) ⁻¹

  i : (n : ℕ) → coHom n D → coHom n A × coHom n B
  i zero = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                λ { δ →  ∣ (λ x → δ (inl x)) ∣₀ , ∣ (λ x → δ (inr x)) ∣₀}
  i (suc n) = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                   λ { δ →  ∣ (λ x → δ (inl x)) ∣₀ , ∣ (λ x → δ (inr x)) ∣₀}

  Δ : (n : ℕ) → coHom n A × coHom n B → coHom n C
  Δ n (α , β) = coHomFun n f α +ₕ -ₕ (coHomFun n g β) -- coHomFun∙2 n f α +ₕ (-ₕ (coHomFun n g β))

  d-pre : (n : ℕ) → (C → coHomK n) → D → coHomK (suc n)
  d-pre n γ (inl x) = 0ₖ
  d-pre n γ (inr x) = 0ₖ
  d-pre zero γ (push a i) = Kn→ΩKn+1 zero (γ a) i
  d-pre (suc n) γ (push a i) = Kn→ΩKn+1 (suc n) (γ a) i

  d : (n : ℕ) → coHom n C → coHom (suc n) D
  d n = sRec setTruncIsSet λ a → ∣ d-pre n a ∣₀

  iIsHom : (n : ℕ) → isMorph (coHomGr n D) (×coHomGr n A B) (i n)
  iIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ f g → refl
  iIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ f g → refl


  prodElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : ∥ A ∥₀ × ∥ B ∥₀ → Type ℓ''}
          → ((x : ∥ A ∥₀ × ∥ B ∥₀) → isOfHLevel 2 (C x))
          → ((a : A) (b : B) → C (∣ a ∣₀ , ∣ b ∣₀))
          → (x : ∥ A ∥₀ × ∥ B ∥₀) → C x
  prodElim {A = A} {B = B} {C = C} hlevel ind (a , b) = schonf a b
    where
    schonf : (a : ∥ A ∥₀) (b : ∥ B ∥₀) → C (a , b)
    schonf = sElim (λ x → isOfHLevelΠ 2 λ y → hlevel (_ , _)) λ a → sElim (λ x → hlevel (_ , _))
                   λ b → ind a b


  prodElim2 : ∀ {ℓ ℓ' ℓ'' ℓ''' ℓ''''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
              {E : (∥ A ∥₀ × ∥ B ∥₀) → (∥ C ∥₀ × ∥ D ∥₀) → Type ℓ''''}
           → ((x : ∥ A ∥₀ × ∥ B ∥₀) (y : ∥ C ∥₀ × ∥ D ∥₀) → isOfHLevel 2 (E x y))
           → ((a : A) (b : B) (c : C) (d : D) → E (∣ a ∣₀ , ∣ b ∣₀) (∣ c ∣₀ , ∣ d ∣₀))
           → ((x : ∥ A ∥₀ × ∥ B ∥₀) (y : ∥ C ∥₀ × ∥ D ∥₀) → (E x y))
  prodElim2 isset f = prodElim (λ _ → isOfHLevelΠ 2 λ _ → isset _ _)
                               λ a b → prodElim (λ _ → isset _ _)
                                       λ c d → f a b c d

  ΔIsHom : (n : ℕ) → isMorph (×coHomGr n A B) (coHomGr n C) (Δ n)
  ΔIsHom zero = prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
                             λ f' x1 g' x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)
  ΔIsHom (suc n) = prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
                             λ f' x1 g' x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)

  dHomHelperPath : (n : ℕ) (h l : C → coHomK n) (a : C) → I → I → coHomK (suc n)
  dHomHelperPath n h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ 0ₖ (~ j)
                    ; (i = i1) → lUnitₖ 0ₖ (~ j)
                    ; (j = i0) → +ₖ→∙ n (h a) (l a) (~ k) i
                    ; (j = i1) → cong₂Funct (λ x y → x +ₖ y) (Kn→ΩKn+1 n (h a)) (Kn→ΩKn+1 n (l a)) (~ k) i})
          (bottom i j)
      where
      bottom : I → I → coHomK (suc n)
      bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ 0ₖ (~ j)
                                   ; (i = i1) → cong (λ x → lUnitₖ x (~ j)) (Kn→ΩKn+1 n (l a)) k})
                         (anotherbottom i j)
        where
        anotherbottom : I → I → coHomK (suc n)
        anotherbottom i j = hcomp (λ k → λ { (i = i0) → rUnitlUnit0 k (~ j)
                                            ; (i = i1) → rUnitlUnit0 k (~ j)
                                            ; (j = i0) → Kn→ΩKn+1 n (h a) i
                                            ; (j = i1) → cong (λ x → x +ₖ 0ₖ) (Kn→ΩKn+1 n (h a)) i})
                                  (cong (λ x → rUnitₖ x (~ j)) (Kn→ΩKn+1 n (h a)) i)


  dHomHelper : (n : ℕ) (h l : C → coHomK n) (x : D) → d-pre n (λ x → h x +ₖ l x) x ≡ d-pre n h x +ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (lUnitₖ 0ₖ)
  dHomHelper n h l (inr x) = sym (lUnitₖ 0ₖ)
  dHomHelper zero h l (push a i) j = dHomHelperPath zero h l a i j
  dHomHelper (suc n) h l (push a i) j = dHomHelperPath (suc n) h l a i j

  dIsHom : (n : ℕ) → isMorph (coHomGr n C) (coHomGr (suc n) D) (d n)
  dIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper zero f g x) i ∣₀
  dIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper (suc n) f g x) i ∣₀


  -- Long Exact Sequence


  Im-d⊂Ker-i : (n : ℕ) (x : coHom (suc n) D) → isInIm (coHomGr n C) (coHomGr (suc n) D) (d n) x → isInKer (coHomGr (suc n) D) (×coHomGr (suc n) A B) (i (suc n)) x
  Im-d⊂Ker-i n = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ a (δ , p) → {!!}
