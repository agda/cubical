{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Properties where

{-
This module contains:
1. direct proofs of connectedness of Kn and ΩKn
2. Induction principles for cohomology groups of pointed types
3. Equivalence between cohomology of A and reduced cohomology of (A + 1)
4. Equivalence between cohomology and reduced cohomology for dimension ≥ 1
5. Encode-decode proof of Kₙ ≃ ΩKₙ₊₁ and proofs that this equivalence
   and its inverse are morphisms
6. A proof of coHomGr ≅ coHomGrΩ
7. A locked (non-reducing) version of Kₙ ≃ ΩKₙ₊₁
8. Some HLevel lemmas used for the cup product
-}


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure

open import Cubical.HITs.S1 hiding (encode ; decode ; _·_)
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Univalence
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; isSetSetTrunc to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_) hiding (-_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group hiding (Unit ; ℤ)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level

cup-pure : {!!}
cup-pure = {!!}
open import Cubical.HITs.S1 renaming (_·_ to _·'_)

S₊3 : S₊ 3 → S₊ 3 → S₊ 3
S₊3 north y = north
S₊3 south y = north
S₊3 (merid north i) north = north
S₊3 (merid south i) north = north
S₊3 (merid (merid base i) j) north = north
S₊3 (merid (merid (loop i₁) i) j) north = north
S₊3 (merid north i) south = north
S₊3 (merid south i) south = north
S₊3 (merid (merid base j) i) south = north
S₊3 (merid (merid (loop k) i) j) south = {!!}
S₊3 (merid north i) (merid north j) = north
S₊3 (merid north i) (merid south j) = north
S₊3 (merid north i) (merid (merid a i₁) j) = {!!}
S₊3 (merid south i) (merid north j) = north
S₊3 (merid south i) (merid south j) = {!north!}
S₊3 (merid south i) (merid (merid a i₁) j) = {!!}
S₊3 (merid (merid a i₁) i) (merid north j) = {!!}
S₊3 (merid (merid a i₁) i) (merid south j) = {!!}
S₊3 (merid (merid a i) j) (merid (merid a₁ k) l) = {!!}

-- open import Cubical.HITs.Join
-- rofl : join S¹ S¹ → Type _
-- rofl (inl x) = {!!}
-- rofl (inr x) = {!!}
-- rofl (push a b i) = {!!}
--   where
--   zz : (x : S₊ 2) → hLevelTrunc 5 (S₊ 3) → hLevelTrunc 5 (S₊ 3)
--   zz x = {!trElim ? ?!}

-- r4 : hLevelTrunc 7 {!!} → {!!} → {!!}
-- r4 = {!!}

-- r3 : hLevelTrunc 6 (S₊ 2) → S₊ 4 → hLevelTrunc 6 (S₊ 2)
-- r3 = trRec (isOfHLevelΠ 6 (λ _ → isOfHLevelTrunc 6))
--            (wedgeconFun 1 3 (λ _ _ → isOfHLevelTrunc 6)
--              {!!} ∣_∣
--              {!!})

-- t : hLevelTrunc 6 (S₊ 3) → hLevelTrunc 5 (S₊ 2) → hLevelTrunc 6 (S₊ 3)
-- t = trRec {!!} {!!}
--   where
--   pp : S₊ 3 → hLevelTrunc 5 (S₊ 2) → hLevelTrunc 6 (S₊ 3)
--   pp north = λ _ → ∣ north ∣
--   pp south = λ _ → ∣ north ∣
--   pp (merid a i) x = {!!}
--     where
--     h : (x : hLevelTrunc 5 (S₊ 2)) → Path (hLevelTrunc 6 (S₊ 3)) ∣ north ∣ ∣ north ∣
--     h = trElim (λ _ → isOfHLevelTrunc 6 _ _)
--                λ b → {!!}

-- S³∥ : Type _
-- S³∥ = hLevelTrunc 6 (S₊ 3)

-- _+3_ : S³∥ → S³∥ → S³∥
-- _+3_ = elim2 (λ _ _ → isOfHLevelTrunc 6) (wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 6)
--                   ∣_∣
--                   ∣_∣
--                   refl)

-- 0₃ : hLevelTrunc 6 (S₊ 3)
-- 0₃ = ∣ north ∣

-- rUnit3 : ∀ x → x +3 0₃ ≡ x
-- rUnit3 = trElim (λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
--                 (wedgeconRight 2 2 {λ _ _ → S³∥}
--                   (λ _ _ → isOfHLevelTrunc 6) ∣_∣ₕ ∣_∣ₕ refl)

-- lUnit3 : ∀ x → 0₃ +3 x ≡ x
-- lUnit3 = trElim (λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
--                 λ _ → refl

-- min3 : hLevelTrunc 6 (S₊ 3) → hLevelTrunc 6 (S₊ 3)
-- min3 = trMap m
--   where
--   m : S₊ 3 → S₊ 3
--   m north = north
--   m south = north
--   m (merid a i) = (merid a ∙ sym (merid north)) i

-- comm3 : ∀ x y → x +3 y ≡ y +3 x
-- comm3 = elim2 (λ _ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
--       (wedgeconFun 2 2
--         (λ _ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
--         (sym ∘ rUnit3 ∘ ∣_∣ₕ)
--         (rUnit3 ∘ ∣_∣ₕ)
--         refl)

-- rCancel3 : (x : hLevelTrunc 6 (S₊ 3)) → x +3 min3 x ≡ 0₃
-- rCancel3 =
--   trElim {!!}
--          λ { north → refl
--            ; south → refl
--            ; (merid a i) → {!!}}
--   where
--   p+ : ∀ {x : S³∥} (p : 0₃ ≡ x) → cong₂ _+3_ p (sym p) ≡ lUnit3 x ∙ sym (rUnit3 x)
--   p+ = J (λ x p → cong₂ _+3_ p (sym p) ≡ lUnit3 x ∙ sym (rUnit3 x)) (rUnit refl)

--   p+merid : ∀ (x : S₊ 2) → cong₂ _+3_ (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid x)))
--                          ≡ {!!}
--   p+merid = {!!}

-- π-iso : Iso (∥ (S₊∙ 4 →∙ (S³∥ , ∣ north ∣)) ∥₂) (∥ (S₊ 4 → S³∥) ∥₂)
-- fun π-iso = map fst
-- inv' π-iso = map λ f → (λ x → (f x) +3 min3 (f north)) , rCancel3 (f north)
-- rightInv π-iso = sElim {!!} {!!}
-- leftInv π-iso = {!!}

-- p2 : Iso ∥ (S₊ 3 → typ (Ω (S³∥ , ∣ north ∣))) ∥₂
--          ∥ (S₊ 2 → typ ((Ω^ 2) (S³∥ , ∣ north ∣))) ∥₂
-- p2 = {!!}

-- data RP2 : Type ℓ-zero where
--   b : RP2
--   l1 l2 : b ≡ b
--   sq : l1 ≡ sym l2

-- rar : S₊ 2 → RP2
-- rar north = b
-- rar south = b
-- rar (merid base i) = (l1 ∙ l2) i
-- rar (merid (loop j) i) =
--   hcomp (λ k → λ { (i = i0) → b
--                   ; (i = i1) → b
--                   ; (j = i0) → (sym (lCancel l2) ∙ cong (_∙ l2) (sym sq)) k i
--                   ; (j = i1) → (sym (lCancel l2) ∙ cong (_∙ l2) (sym sq)) k i})
--         b



-- jmap : join S¹ S¹ → S₊ 2
-- jmap (inl x) = north
-- jmap (inr x) = south
-- jmap (push a b₁ i) = merid (a ·' b₁) i

-- gl : Susp (join S¹ S¹) → S₊ 3
-- gl north = north
-- gl south = south
-- gl (merid a i) = merid (jmap a) i

-- _+j_ : (Susp (join S¹ S¹) , north) →∙ S₊∙ 3
--      → (Susp (join S¹ S¹) , north) →∙ S₊∙ 3
--      → (Susp (join S¹ S¹) , north) →∙ S₊∙ 3
-- fst (f +j g) north = north
-- fst (f +j g) south = north
-- fst (f +j g) (merid a i) =
--   ((sym (snd f) ∙∙ cong (fst f) (merid a ∙ sym (merid (inl base))) ∙∙ snd f)
--   ∙ ((sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid (inl base))) ∙∙ snd g))) i
-- snd (f +j g) = refl

-- ss123 : {!!}
-- ss123 = {!!}

-- thegen : {!(Susp (join S¹ S¹) , north) →∙ S₊∙ 3!}
-- thegen = {!!}

-- thegen2 : (Susp (join S¹ S¹) , north) →∙ (S³∥ , ∣ north ∣)
-- fst thegen2 north = ∣ north ∣
-- fst thegen2 south = ∣ north ∣
-- fst thegen2 (merid a i) =
--   ∣ (cong gl (merid a ∙ sym (merid (inl base)))
--   ∙ cong gl (merid a ∙ sym (merid (inl base)))) i ∣
-- snd thegen2 = refl

-- s : join S¹ S¹ → {!!}
-- s = {!!}

-- rs : (x : _) → fst thegen2 x ≡  ∣ north ∣
-- rs north = refl
-- rs south = refl
-- rs (merid a i) j = pp a j i
--   where
--   open import Cubical.HITs.Wedge
--   wedge→gpd : ∀ {ℓ} (P : (S₊∙ 1) ⋁ S₊∙ 1 → Type ℓ)
--             → ((s : (S₊∙ 1) ⋁ S₊∙ 1) → isGroupoid (P s)) 
--             → {!!}
--             → {!!}
--   wedge→gpd = {!!}

--   pp3 : (a : join S¹ S¹) →
--     cong (∣_∣ₕ {n = 6}) (cong gl (merid a ∙ sym (merid (inl base)))) ≡
--       sym (cong (∣_∣ₕ {n = 6}) (cong gl (merid a ∙ sym (merid (inl base))))) -- 4
--   pp3 (inl x) = {!!}
--   pp3 (inr x) = {!!}
--   pp3 (push a b₁ i) = {!!} -- 3

--   pp4 : (a : join S¹ S¹) → cong (∣_∣ₕ {n = 6}) (merid (jmap a) ∙ sym (merid north))
--                          ≡ sym (cong (∣_∣ₕ {n = 6}) (merid (jmap a) ∙ sym (merid north)))
--                          -- 4-type
--   pp4 (inl x) = cong (cong (∣_∣ₕ {n = 6})) (rCancel (merid north))
--               ∙ cong sym (cong (cong (∣_∣ₕ {n = 6})) (sym (rCancel (merid north))))
--   pp4 (inr x) = (cong (cong (∣_∣ₕ {n = 6})) λ i → merid (merid base (~ i)) ∙ sym (merid north))
--               ∙∙ (cong (cong (∣_∣ₕ {n = 6})) (rCancel (merid north))
--               ∙ cong sym (cong (cong (∣_∣ₕ {n = 6})) (sym (rCancel (merid north)))))
--               ∙∙ cong sym (cong (cong (∣_∣ₕ {n = 6}))
--                           λ i → merid (merid base i) ∙ sym (merid north))
--                           -- 3-type
--   pp4 (push a c i) j k = {!!}
--     where
--     c' : ∥ cong merid (merid a) ≡ cong merid (merid base) ∥ 1
--     c' = isConnectedPath _ (isConnectedPath 2 (isConnectedPath 3 (sphereConnected 3) _ _) _ _) _ _ .fst

--     pr : (a c : S¹) → cong merid (merid (a ·' c)) ≡ cong merid (merid a ∙ sym (merid c))
--                                                         ∙ (cong merid (merid base))
--     pr base base = {!!}
--     pr base (loop i) = {!!}
--     pr (loop i) base = {!cong ∣_∣ₕ (merid (cong jmap (push a c)) ∙ sym (merid north))!}
--     pr (loop i) (loop j) = {!!}

--     hej : Cube (λ j → cong ∣_∣ₕ (merid (merid (a ·' c) j) ∙ sym (merid north))) -- i j k
--                (λ j → cong ∣_∣ₕ (merid (merid a j) ∙ sym (merid (merid c j))))
--                {!!}
--                {!!}
--                {!!}
--                {!!}
--     hej = {!!}
--   pp : (a : join S¹ S¹) →
--     cong (∣_∣ₕ {n = 6}) ((cong gl (merid a ∙ sym (merid (inl base)))
--       ∙ cong gl (merid a ∙ sym (merid (inl base))))) ≡ refl
--   pp a = {!merid a!} ∙ {!!}
-- +gen : ℤ → (Susp (join S¹ S¹) , north) →∙ S₊∙ 3
-- +gen (pos zero) = (λ x → north) , refl
-- fst (+gen (pos (suc n))) north = north
-- fst (+gen (pos (suc n))) south = north
-- fst (+gen (pos (suc n))) (merid a i) =
--   {!cong (fst (+gen (pos n))) (merid a ∙ sym (merid (inl base)))!}
-- snd (+gen (pos (suc n))) = {!!}
-- +gen (negsuc zero) = {!!}
-- +gen (negsuc (suc n)) = {!!}

-- _+∙_ : {!!} -- {n m : ℕ} → (S₊∙ n → S₊∙ m) → (S₊∙ n → S₊∙ m) → (S₊∙ n → S₊∙ m)
-- _+∙_ = {!!}

-- sn : Iso ∥ (typ ((Ω^ 4) (S₊∙ 3))) ∥₂
--         (∥ (Σ[ x ∈ typ ((Ω^ 3) (S₊∙ 3)) ]
--           x ≡ sym x) ∥₂)
-- fun sn = map λ p → (λ i j k → p (i ∨ j) (j ∨ k) (k ∨ i) (~ k ∨ ~ i ∨ ~ j))
--                  , {!!}
-- inv' sn = {!!}
-- rightInv sn = {!!}
-- leftInv sn = {!!}

-- gaza : ∥ {!!} ≃ {!!} ∥₂
-- gaza = {!!}

-- Σ- : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
-- Σ- north = south
-- Σ- south = north
-- Σ- (merid a i) = merid a (~ i)

-- rr : Iso (∥ (Σ[ f ∈ S₊∙ 3 →∙ (S³∥ , ∣ north ∣) ] ((x : S₊ 3) → fst f x ≡ fst f x)) ∥₂)
--          (∥ (Σ[ f ∈ S₊∙ 3 →∙ coHomK-ptd 3 ] ((x : S₊ 3) → fst f x +ₖ fst f x ≡ 0ₖ 3)) ∥₂)
-- fun rr = {!sMap ?!}
-- inv' rr = {!!}
-- rightInv rr = {!!}
-- leftInv rr = {!!}

-- open import Cubical.HITs.Pushout
-- RP3 : Type ℓ-zero
-- RP3 = Pushout rar λ _ → tt

-- RP4 : S₊ 3 → RP3
-- RP4 north = inl b
-- RP4 south = inr tt
-- RP4 (merid north i) = push north i
-- RP4 (merid south i) = push south i
-- RP4 (merid (merid base j) i) = push {!rar!} i
-- RP4 (merid (merid (loop k) j) i) = {!!}

-- ll : hLevelTrunc 5 (S₊ 2) → hLevelTrunc 5 (S₊ 2) → {!!}
-- ll = {!!}

-- ss : Iso ∥ (S₊ 1 → (S₊∙ 1 →∙ ((Ω^ 2) (S³∥ , ∣ north ∣)))) ∥₂
--          ∥ ((S₊ 1 → (S₊ 1 → typ ((Ω^ 2) (S³∥ , ∣ north ∣))))) ∥₂
-- fun ss = map λ f → λ x y → f x .fst y
-- inv' ss = map λ f x → {!f!}
-- rightInv ss = {!!}
-- leftInv ss = {!!}

-- p3 : Iso ∥ (S₊ 2 → coHomK-ptd 1 →∙ (coHomK-ptd 1 →∙ S³∥ , ∣ north ∣ ∙)) ∥₂
--          ∥ {!!} ∥₂
-- p3 = {!S₊∙ 3 !}

-- cong2 : {!!}
-- cong2 = {!!}

-- -- ------------------- Connectedness ---------------------
-- -- is2ConnectedKn : (n : ℕ) → isConnected 2 (coHomK (suc n))
-- -- is2ConnectedKn zero = ∣ ∣ base ∣ ∣
-- --                     , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
-- --                         (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
-- --                           (toPropElim (λ _ → isOfHLevelTrunc 2 _ _) refl))
-- -- is2ConnectedKn (suc n) = ∣ ∣ north ∣ ∣
-- --                        , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
-- --                            (trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isOfHLevelTrunc 2 _ _))
-- --                              (suspToPropElim (ptSn (suc n)) (λ _ → isOfHLevelTrunc 2 _ _) refl))

-- -- isConnectedKn : (n : ℕ) → isConnected (2 + n) (coHomK (suc n))
-- -- isConnectedKn n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (2 + n) 1)) (sphereConnected (suc n))

-- -- -- direct proof of connectedness of ΩKₙ₊₁ not relying on the equivalence ∥ a ≡ b ∥ₙ ≃ (∣ a ∣ₙ₊₁ ≡ ∣ b ∣ₙ₊₁)
-- -- isConnectedPathKn : (n : ℕ) (x y : (coHomK (suc n))) → isConnected (suc n) (x ≡ y)
-- -- isConnectedPathKn n =
-- --   trElim (λ _ → isProp→isOfHLevelSuc (2 + n) (isPropΠ λ _ → isPropIsContr))
-- --     (sphereElim _ (λ _ → isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr))
-- --       λ y → isContrRetractOfConstFun
-- --                {B = (hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n)))} ∣ refl ∣
-- --                  (fun⁻ n y
-- --                 , trElim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
-- --                          (J (λ y p → fun⁻ n y _ ≡ _) (funExt⁻ (fun⁻Id n) ∣ refl ∣))))
-- --   where
-- --   fun⁻ : (n : ℕ) → (y : coHomK (suc n)) →
-- --          hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n))
-- --       → hLevelTrunc (suc n) (∣ ptSn (suc n) ∣ ≡ y)
-- --   fun⁻ n =
-- --     trElim (λ _ → isOfHLevelΠ (3 + n) λ _ → isOfHLevelSuc (2 + n) (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n))))
-- --       (sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelTrunc (suc n)) λ _ → ∣ refl ∣)

-- --   fun⁻Id : (n : ℕ) → fun⁻ n ∣ ptSn (suc n) ∣ ≡ λ _ → ∣ refl ∣
-- --   fun⁻Id zero = refl
-- --   fun⁻Id (suc n) = refl

-- -- -------------------
-- -- -- Induction principles for cohomology groups (n ≥ 1)
-- -- -- If we want to show a proposition about some x : Hⁿ(A), it suffices to show it under the
-- -- -- assumption that x = ∣ f ∣₂ for some f : A → Kₙ and that f is pointed

-- -- coHomPointedElim : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → Type ℓ'}
-- --                  → ((x : coHom (suc n) A) → isProp (B x))
-- --                  → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
-- --                  → (x : coHom (suc n) A) → B x
-- -- coHomPointedElim {ℓ' = ℓ'} {A = A} n a isprop indp =
-- --   sElim (λ _ → isOfHLevelSuc 1 (isprop _))
-- --          λ f → helper n isprop indp f (f a) refl
-- --   where
-- --   helper :  (n : ℕ) {B : coHom (suc n) A → Type ℓ'}
-- --          → ((x : coHom (suc n) A) → isProp (B x))
-- --          → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
-- --          → (f : A → coHomK (suc n))
-- --          → (x : coHomK (suc n))
-- --          → f a ≡ x → B ∣ f ∣₂
-- --   -- pattern matching a bit extra to avoid isOfHLevelPlus'
-- --   helper zero isprop ind f =
-- --     trElim (λ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ λ _ → isprop _))
-- --            (toPropElim (λ _ → isPropΠ λ _ → isprop _) (ind f))
-- --   helper (suc zero) isprop ind f =
-- --     trElim (λ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ λ _ → isprop _))
-- --            (suspToPropElim base (λ _ → isPropΠ λ _ → isprop _) (ind f))
-- --   helper (suc (suc zero)) isprop ind f =
-- --     trElim (λ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ λ _ → isprop _))
-- --            (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))
-- --   helper (suc (suc (suc n))) isprop ind f =
-- --     trElim (λ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ λ _ → isprop _))
-- --            (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))


-- -- coHomPointedElim2 : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
-- --                  → ((x y : coHom (suc n) A) → isProp (B x y))
-- --                  → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
-- --                  → (x y : coHom (suc n) A) → B x y
-- -- coHomPointedElim2 {ℓ' = ℓ'} {A = A} n a isprop indp = sElim2 (λ _ _ → isOfHLevelSuc 1 (isprop _ _))
-- --                                                    λ f g → helper n a isprop indp f g (f a) (g a) refl refl
-- --   where
-- --   helper : (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
-- --                  → ((x y : coHom (suc n) A) → isProp (B x y))
-- --                  → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
-- --                  → (f g : A → coHomK (suc n))
-- --                  → (x y : coHomK (suc n))
-- --                  → f a ≡ x → g a ≡ y
-- --                  → B ∣ f ∣₂ ∣ g ∣₂
-- --   helper zero a isprop indp f g =
-- --     elim2 (λ _ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ2 λ _ _ → isprop _ _))
-- --           (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
-- --   helper (suc zero) a isprop indp f g =
-- --     elim2 (λ _ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ2 λ _ _ → isprop _ _))
-- --           (suspToPropElim2 base (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
-- --   helper (suc (suc zero)) a isprop indp f g =
-- --     elim2 (λ _ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ2 λ _ _ → isprop _ _))
-- --           (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
-- --   helper (suc (suc (suc n))) a isprop indp f g =
-- --     elim2 (λ _ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ2 λ _ _ → isprop _ _))
-- --           (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))

-- -- coHomK-elim : ∀ {ℓ} (n : ℕ) {B : coHomK (suc n) → Type ℓ}
-- --            → ((x : _) → isOfHLevel (suc n) (B x))
-- --            → B (0ₖ (suc n))
-- --            → (x : _) → B x
-- -- coHomK-elim n {B = B } hlev b =
-- --   trElim (λ _ → isOfHLevelPlus {n = (suc n)} 2 (hlev _))
-- --     (sphereElim _ (hlev ∘ ∣_∣) b)

-- -- {- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
-- -- coHomRed+1Equiv : (n : ℕ) →
-- --                   (A : Type ℓ) →
-- --                   (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
-- -- coHomRed+1Equiv zero A i = ∥ helpLemma {C = (ℤ , pos 0)} i ∥₂
-- --   module coHomRed+1 where
-- --   helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
-- --   helpLemma {C = C} = isoToPath (iso map1
-- --                                      map2
-- --                                      (λ b → linvPf b)
-- --                                      (λ _  → refl))
-- --     where
-- --     map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
-- --     map1 f = map1' , refl
-- --       module helpmap where
-- --       map1' : A ⊎ Unit → fst C
-- --       map1' (inl x) = f x
-- --       map1' (inr x) = pt C

-- --     map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
-- --     map2 (g , pf) x = g (inl x)

-- --     linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
-- --     linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
-- --       where
-- --       helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
-- --       helper (inl x) = refl
-- --       helper (inr tt) = sym snd
-- -- coHomRed+1Equiv (suc zero) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK 1 , ∣ base ∣)} i ∥₂
-- -- coHomRed+1Equiv (suc (suc n)) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK (2 + n) , ∣ north ∣)} i ∥₂

-- -- Iso-coHom-coHomRed : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → Iso (coHomRed (suc n) A) (coHom (suc n) (typ A))
-- -- fun (Iso-coHom-coHomRed {A = A , a} n) = map fst
-- -- inv' (Iso-coHom-coHomRed {A = A , a} n) = map λ f → (λ x → f x -ₖ f a) , rCancelₖ _ _
-- -- rightInv (Iso-coHom-coHomRed {A = A , a} n) =
-- --   sElim (λ _ → isOfHLevelPath 2 § _ _)
-- --          λ f → trRec (isProp→isOfHLevelSuc _ (§ _ _))
-- --                       (λ p → cong ∣_∣₂ (funExt λ x → cong (λ y → f x +ₖ y) (cong -ₖ_ p ∙ -0ₖ) ∙ rUnitₖ _ (f x)))
-- --                       (Iso.fun (PathIdTruncIso (suc n)) (isContr→isProp (isConnectedKn n) ∣ f a ∣ ∣ 0ₖ _ ∣))
-- -- leftInv (Iso-coHom-coHomRed {A = A , a} n) =
-- --   sElim (λ _ → isOfHLevelPath 2 § _ _)
-- --         λ {(f , p) → cong ∣_∣₂ (ΣPathP (((funExt λ x → (cong (λ y → f x -ₖ y) p
-- --                                                     ∙∙ cong (λ y → f x +ₖ y) -0ₖ
-- --                                                     ∙∙ rUnitₖ _ (f x)) ∙ refl))
-- --                               , helper n (f a) (sym p)))}
-- --     where
-- --     path : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x) → _
-- --     path n x p = (cong (λ y → x -ₖ y) (sym p) ∙∙ cong (λ y → x +ₖ y) -0ₖ ∙∙ rUnitₖ _ x) ∙ refl

-- --     helper :  (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x)
-- --             → PathP (λ i → path n x p i ≡ 0ₖ _) (rCancelₖ _ x) (sym p)
-- --     helper zero x =
-- --       J (λ x p → PathP (λ i → path 0 x p i ≡ 0ₖ _)
-- --                         (rCancelₖ _ x) (sym p))
-- --         λ i j → rUnit (rUnit (λ _ → 0ₖ 1) (~ j)) (~ j) i
-- --     helper (suc n) x =
-- --       J (λ x p → PathP (λ i → path (suc n) x p i ≡ 0ₖ _) (rCancelₖ _ x) (sym p))
-- --         λ i j → rCancelₖ (suc (suc n)) (0ₖ (suc (suc n))) (~ i ∧ ~ j)

-- -- +∙≡+ : (n : ℕ) {A : Pointed ℓ} (x y : coHomRed (suc n) A)
-- --      → Iso.fun (Iso-coHom-coHomRed n) (x +ₕ∙ y)
-- --       ≡ Iso.fun (Iso-coHom-coHomRed n) x +ₕ Iso.fun (Iso-coHom-coHomRed n) y

-- -- +∙≡+ zero = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl
-- -- +∙≡+ (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl

-- -- private
-- --   homhelp : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) (x y : coHom (suc n) (typ A))
-- --           → Iso.inv (Iso-coHom-coHomRed {A = A} n) (x +ₕ y)
-- --            ≡ Iso.inv (Iso-coHom-coHomRed n) x +ₕ∙ Iso.inv (Iso-coHom-coHomRed n) y
-- --   homhelp n A = morphLemmas.isMorphInv _+ₕ∙_ _+ₕ_
-- --                 (Iso.fun (Iso-coHom-coHomRed n)) (+∙≡+ n) _
-- --                 (Iso.rightInv (Iso-coHom-coHomRed n)) (Iso.leftInv (Iso-coHom-coHomRed n))

-- -- coHomGr≅coHomRedGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
-- --                   → GroupEquiv (coHomRedGrDir (suc n) A) (coHomGr (suc n) (typ A))
-- -- fst (coHomGr≅coHomRedGr n A) = isoToEquiv (Iso-coHom-coHomRed n)
-- -- snd (coHomGr≅coHomRedGr n A) = makeIsGroupHom (+∙≡+ n)

-- -- coHomRedGroup : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → AbGroup ℓ
-- -- coHomRedGroup zero A = coHomRedGroupDir zero A
-- -- coHomRedGroup (suc n) A =
-- --   InducedAbGroup (coHomGroup (suc n) (typ A))
-- --                  _+ₕ∙_
-- --                  (isoToEquiv (invIso (Iso-coHom-coHomRed n)))
-- --                  (homhelp n A)

-- -- abstract
-- --   coHomGroup≡coHomRedGroup : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
-- --                           → coHomGroup (suc n) (typ A) ≡ coHomRedGroup (suc n) A
-- --   coHomGroup≡coHomRedGroup n A =
-- --     InducedAbGroupPath (coHomGroup (suc n) (typ A))
-- --               _+ₕ∙_
-- --               (isoToEquiv (invIso (Iso-coHom-coHomRed n)))
-- --               (homhelp n A)

-- -- ------------------- Kₙ ≃ ΩKₙ₊₁ ---------------------
-- -- -- This proof uses the encode-decode method rather than Freudenthal

-- -- -- We define the map σ : Kₙ → ΩKₙ₊₁ and prove that it is a morphism
-- -- private
-- --   module _ (n : ℕ) where
-- --   σ : {n : ℕ} → coHomK (suc n) → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
-- --   σ {n = n} = trRec (isOfHLevelTrunc (4 + n) _ _)
-- --                     λ a → cong ∣_∣ (merid a ∙ sym (merid (ptSn (suc n))))

-- --   σ-hom-helper : ∀ {ℓ} {A : Type ℓ} {a : A} (p : a ≡ a) (r : refl ≡ p)
-- --                    → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r
-- --   σ-hom-helper p = J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

-- --   σ-hom : {n : ℕ} (x y : coHomK (suc n)) → σ (x +ₖ y) ≡ σ x ∙ σ y
-- --   σ-hom {n = zero} =
-- --     elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
-- --           (wedgeconFun _ _
-- --             (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
-- --             (λ x → lUnit _
-- --                   ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
-- --             (λ y → cong σ (rUnitₖ 1 ∣ y ∣)
-- --                  ∙∙ rUnit _
-- --                  ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
-- --             (sym (σ-hom-helper (σ ∣ base ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))))
-- --   σ-hom {n = suc n} =
-- --     elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
-- --           (wedgeconFun _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
-- --            (λ x → lUnit _
-- --                  ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
-- --            (λ y → cong σ (rUnitₖ (2 + n) ∣ y ∣)
-- --                 ∙∙ rUnit _
-- --                 ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
-- --            (sym (σ-hom-helper (σ ∣ north ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))))

-- --   -- We will need to following lemma
-- --   σ-minusDistr : {n : ℕ} (x y : coHomK (suc n)) → σ (x -ₖ y) ≡ σ x ∙ sym (σ y)
-- --   σ-minusDistr {n = n} =
-- --     morphLemmas.distrMinus'
-- --       _+ₖ_ _∙_
-- --       σ σ-hom ∣ (ptSn (suc n)) ∣ refl
-- --       -ₖ_ sym
-- --       (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
-- --       (rUnitₖ (suc n))
-- --       (lCancelₖ (suc n)) rCancel
-- --       (assocₖ (suc n)) assoc∙
-- --        (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

-- --   -- we define the code using addIso
-- --   Code : (n : ℕ) →  coHomK (2 + n) → Type₀
-- --   Code n x = (trRec {B = TypeOfHLevel ℓ-zero (3 + n)} (isOfHLevelTypeOfHLevel (3 + n))
-- --                      λ a → Code' a , hLevCode' a) x .fst
-- --     where
-- --     Code' : (S₊ (2 + n)) → Type₀
-- --     Code' north = coHomK (suc n)
-- --     Code' south = coHomK (suc n)
-- --     Code' (merid a i) = isoToPath (addIso (suc n) ∣ a ∣) i

-- --     hLevCode' : (x : S₊ (2 + n)) → isOfHLevel (3 + n) (Code' x)
-- --     hLevCode' = suspToPropElim (ptSn (suc n)) (λ _ → isPropIsOfHLevel (3 + n)) (isOfHLevelTrunc (3 + n))

-- --   symMeridLem : (n : ℕ) → (x : S₊ (suc n)) (y : coHomK (suc n))
-- --                         → subst (Code n) (cong ∣_∣ (sym (merid x))) y ≡ y -ₖ ∣ x ∣
-- --   symMeridLem n x = trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
-- --                             (λ y → cong (_-ₖ ∣ x ∣) (transportRefl ∣ y ∣))

-- --   decode : {n : ℕ} (x : coHomK (2 + n)) → Code n x → ∣ north ∣ ≡ x
-- --   decode {n = n} = trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
-- --                           decode-elim
-- --     where
-- --     north≡merid : (a : S₊ (suc n))
-- --                 → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
-- --                 ≡ (Path (coHomK (2 + n)) ∣ north ∣ ∣ south ∣)
-- --     north≡merid a i = Path (coHomK (2 + n)) ∣ north ∣ ∣ merid a i ∣

-- --     decode-elim : (a : S₊ (2 + n)) → Code n ∣ a ∣ → Path (coHomK (2 + n)) ∣ north ∣ ∣ a ∣
-- --     decode-elim north = σ
-- --     decode-elim south = trRec (isOfHLevelTrunc (4 + n) _ _)
-- --                               λ a → cong ∣_∣ (merid a)
-- --     decode-elim (merid a i) =
-- --       hcomp (λ k → λ { (i = i0) → σ
-- --                       ; (i = i1) → mainPath a k})
-- --             (funTypeTransp (Code n) (λ x → ∣ north ∣ ≡ x) (cong ∣_∣ (merid a)) σ i)
-- --       where
-- --       mainPath : (a : (S₊ (suc n))) →
-- --              transport (north≡merid a) ∘ σ ∘ transport (λ i → Code n ∣ merid a (~ i) ∣)
-- --            ≡ trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a)
-- --       mainPath a = funExt (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
-- --                                   (λ x → (λ i → transport (north≡merid a) (σ (symMeridLem n a ∣ x ∣ i)))
-- --                                        ∙∙ cong (transport (north≡merid a)) (-distrHelp x)
-- --                                        ∙∙ (substAbove x)))
-- --         where
-- --         -distrHelp : (x : S₊ (suc n)) → σ (∣ x ∣ -ₖ ∣ a ∣) ≡ cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a))
-- --         -distrHelp x =
-- --              σ-minusDistr ∣ x ∣ ∣ a ∣
-- --            ∙ (λ i → (cong ∣_∣ (compPath-filler (merid x) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))
-- --                    ∙ (cong ∣_∣ (sym (compPath-filler (merid a) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))))

-- --         substAbove : (x : S₊ (suc n)) → transport (north≡merid a) (cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a)))
-- --                    ≡ cong ∣_∣ (merid x)
-- --         substAbove x i = transp (λ j → north≡merid a (i ∨ j)) i
-- --                                 (compPath-filler (cong ∣_∣ (merid x)) (λ j → ∣ merid a (~ j ∨ i) ∣) (~ i))

-- --   encode : {n : ℕ} {x : coHomK (2 + n)} → Path (coHomK (2 + n)) ∣ north ∣ x → Code n x
-- --   encode {n = n} p = transport (cong (Code n) p) ∣ (ptSn (suc n)) ∣

-- --   decode-encode : {n : ℕ} {x : coHomK (2 + n)} (p : Path (coHomK (2 + n)) ∣ north ∣ x)
-- --                → decode _ (encode p) ≡ p
-- --   decode-encode {n = n} =
-- --     J (λ y p → decode _ (encode p) ≡ p)
-- --         (cong (decode ∣ north ∣) (transportRefl ∣ ptSn (suc n) ∣)
-- --        ∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

-- -- -- We define an addition operation on Code which we can use in order to show that encode is a
-- -- -- morphism (in a very loose sense)
-- --   hLevCode : {n : ℕ} (x : coHomK (2 + n)) → isOfHLevel (3 + n) (Code n x)
-- --   hLevCode {n = n} =
-- --     trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropIsOfHLevel (3 + n)))
-- --       (sphereToPropElim _
-- --         (λ _ → (isPropIsOfHLevel (3 + n))) (isOfHLevelTrunc (3 + n)))

-- --   Code-add' : {n : ℕ} (x : _) → Code n ∣ north ∣ → Code n ∣ x ∣ → Code n ∣ x ∣
-- --   Code-add' {n = n} north = _+ₖ_
-- --   Code-add' {n = n} south = _+ₖ_
-- --   Code-add' {n = n} (merid a i) = helper n a i
-- --     where
-- --     help : (n : ℕ) → (x y a : S₊ (suc n))
-- --         → transport (λ i → Code n ∣ north ∣ → Code n ∣ merid a i ∣ → Code n ∣ merid a i ∣)
-- --                      (_+ₖ_) ∣ x ∣ ∣ y ∣
-- --          ≡ ∣ x ∣ +ₖ ∣ y ∣
-- --     help n x y a =
-- --          (λ i → transportRefl ((∣ transportRefl x i ∣  +ₖ (∣ transportRefl y i ∣ -ₖ ∣ a ∣)) +ₖ ∣ a ∣) i)
-- --       ∙∙ cong (_+ₖ ∣ a ∣) (assocₖ _ ∣ x ∣ ∣ y ∣ (-ₖ ∣ a ∣))
-- --       ∙∙ sym (assocₖ _ (∣ x ∣ +ₖ ∣ y ∣) (-ₖ ∣ a ∣) ∣ a ∣)
-- --       ∙∙ cong ((∣ x ∣ +ₖ ∣ y ∣) +ₖ_) (lCancelₖ _ ∣ a ∣)
-- --       ∙∙ rUnitₖ _ _

-- --     helper : (n : ℕ) (a : S₊ (suc n))
-- --            → PathP (λ i → Code n ∣ north ∣ → Code n ∣ merid a i ∣ → Code n ∣ merid a i ∣) _+ₖ_ _+ₖ_
-- --     helper n a =
-- --       toPathP (funExt
-- --                 (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelΠ (3 + n) (λ _ → isOfHLevelTrunc (3 + n))) _ _)
-- --                   λ x → funExt
-- --                            (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
-- --                                    λ y → help n x y a)))

-- --   Code-add : {n : ℕ} (x : _) → Code n ∣ north ∣ → Code n x → Code n x
-- --   Code-add {n = n} =
-- --     trElim (λ x → isOfHLevelΠ (4 + n) λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelSuc (3 + n) (hLevCode {n = n} x))
-- --            Code-add'

-- --   encode-hom : {n : ℕ} {x : _} (q : 0ₖ _ ≡ 0ₖ _) (p : 0ₖ _ ≡ x)
-- --              → encode (q ∙ p) ≡ Code-add {n = n} x (encode q) (encode p)
-- --   encode-hom {n = n} q = J (λ x p → encode (q ∙ p) ≡ Code-add {n = n} x (encode q) (encode p))
-- --                            (cong encode (sym (rUnit q))
-- --                          ∙∙ sym (rUnitₖ _ (encode q))
-- --                          ∙∙ cong (encode q +ₖ_) (cong ∣_∣ (sym (transportRefl _))))

-- -- stabSpheres : (n : ℕ) → Iso (coHomK (suc n)) (typ (Ω (coHomK-ptd (2 + n))))
-- -- fun (stabSpheres n) = decode _
-- -- inv' (stabSpheres n) = encode
-- -- rightInv (stabSpheres n) p = decode-encode p
-- -- leftInv (stabSpheres n) =
-- --   trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
-- --     λ a → cong encode (congFunct ∣_∣ (merid a) (sym (merid (ptSn (suc n)))))
-- --         ∙∙ (λ i → transport (congFunct (Code n) (cong ∣_∣ (merid a))
-- --                              (cong ∣_∣ (sym (merid (ptSn (suc n))))) i) ∣ ptSn (suc n) ∣)
-- --         ∙∙ (substComposite (λ x → x)
-- --                            (cong (Code n) (cong ∣_∣ (merid a)))
-- --                            (cong (Code n) (cong ∣_∣ (sym (merid (ptSn (suc n)))))) ∣ ptSn (suc n) ∣
-- --         ∙∙ cong (transport (λ i → Code n ∣ merid (ptSn (suc n)) (~ i) ∣))
-- --                 (transportRefl (∣ (ptSn (suc n)) ∣ +ₖ ∣ a ∣) ∙ lUnitₖ (suc n) ∣ a ∣)
-- --         ∙∙ symMeridLem n (ptSn (suc n)) ∣ a ∣
-- --         ∙∙ cong (∣ a ∣ +ₖ_) -0ₖ
-- --         ∙∙ rUnitₖ (suc n) ∣ a ∣)

-- -- Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
-- -- Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS¹)) ΩS¹Isoℤ)
-- -- Iso-Kn-ΩKn+1 (suc n) = stabSpheres n

-- -- Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
-- -- Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

-- -- -- Some properties of the Iso
-- -- Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
-- -- Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

-- -- ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
-- -- ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

-- -- Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
-- -- Kn→ΩKn+10ₖ zero = sym (rUnit refl)
-- -- Kn→ΩKn+10ₖ (suc n) i j = ∣ (rCancel (merid (ptSn (suc n))) i j) ∣

-- -- ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
-- -- ΩKn+1→Kn-refl zero = refl
-- -- ΩKn+1→Kn-refl (suc zero) = refl
-- -- ΩKn+1→Kn-refl (suc (suc n)) = refl

-- -- Kn≃ΩKn+1∙ : {n : ℕ} → coHomK-ptd n ≡ (Ω (coHomK-ptd (suc n)))
-- -- Kn≃ΩKn+1∙ {n = n} = ua∙ Kn≃ΩKn+1 (Kn→ΩKn+10ₖ n)

-- -- Kn→ΩKn+1-hom : (n : ℕ) (x y : coHomK n) → Kn→ΩKn+1 n (x +[ n ]ₖ y) ≡ Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y
-- -- Kn→ΩKn+1-hom zero x y = (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
-- --                                          (inS (∣ intLoop (x ℤ+ y) i ∣)) (~ j))
-- --                       ∙∙ (λ j i → ∣ intLoop-hom x y (~ j) i ∣)
-- --                       ∙∙ (congFunct ∣_∣ (intLoop x) (intLoop y)
-- --                         ∙ cong₂ _∙_ (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
-- --                                                     (inS (∣ intLoop x i ∣)) j)
-- --                                      λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
-- --                                                     (inS (∣ intLoop y i ∣)) j)
-- -- Kn→ΩKn+1-hom (suc n) = σ-hom

-- -- ΩKn+1→Kn-hom : (n : ℕ) (x y : Path (coHomK (suc n)) (0ₖ _) (0ₖ _))
-- --              → ΩKn+1→Kn n (x ∙ y) ≡ ΩKn+1→Kn n x +[ n ]ₖ ΩKn+1→Kn n y
-- -- ΩKn+1→Kn-hom zero p q =
-- --      cong winding (congFunct (trRec isGroupoidS¹ (λ x → x)) p q)
-- --    ∙ winding-hom (cong (trRec isGroupoidS¹ (λ x → x)) p) (cong (trRec isGroupoidS¹ (λ x → x)) q)
-- -- ΩKn+1→Kn-hom (suc n) = encode-hom

-- -- Kn→ΩKn+1-ₖ : (n : ℕ) (x : coHomK n) → Kn→ΩKn+1 n (-ₖ x) ≡ sym (Kn→ΩKn+1 n x)
-- -- Kn→ΩKn+1-ₖ n x =
-- --      lUnit _
-- --   ∙∙ cong (_∙ Kn→ΩKn+1 n (-ₖ x)) (sym (lCancel _))
-- --   ∙∙ sym (assoc∙ _ _ _)
-- --   ∙∙ cong (sym (Kn→ΩKn+1 n x) ∙_) help
-- --   ∙∙ sym (rUnit _)
-- --   where
-- --   help : Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n (-ₖ x) ≡ refl
-- --   help = sym (Kn→ΩKn+1-hom n x (-ₖ x)) ∙∙ cong (Kn→ΩKn+1 n) (rCancelₖ n x) ∙∙ Kn→ΩKn+10ₖ n

-- -- isHomogeneousKn : (n : HLevel) → isHomogeneous (coHomK-ptd n)
-- -- isHomogeneousKn n =
-- --   subst isHomogeneous
-- --     (sym (ΣPathP (ua Kn≃ΩKn+1 , ua-gluePath _ (Kn→ΩKn+10ₖ n))))
-- --     (isHomogeneousPath _ _)

-- -- -- With the equivalence Kn≃ΩKn+1, we get that the two definitions of cohomology groups agree
-- -- open IsGroupHom

-- -- coHom≅coHomΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → GroupIso (coHomGr n A) (coHomGrΩ n A)
-- -- fun (fst (coHom≅coHomΩ n A)) = map λ f a → Kn→ΩKn+1 n (f a)
-- -- inv' (fst (coHom≅coHomΩ n A)) = map λ f a → ΩKn+1→Kn n (f a)
-- -- rightInv (fst (coHom≅coHomΩ n A)) =
-- --   sElim (λ _ → isOfHLevelPath 2 § _ _)
-- --         λ f → cong ∣_∣₂ (funExt λ x → rightInv (Iso-Kn-ΩKn+1 n) (f x))
-- -- leftInv (fst (coHom≅coHomΩ n A)) =
-- --   sElim (λ _ → isOfHLevelPath 2 § _ _)
-- --         λ f → cong ∣_∣₂ (funExt λ x → leftInv (Iso-Kn-ΩKn+1 n) (f x))
-- -- snd (coHom≅coHomΩ n A) =
-- --   makeIsGroupHom
-- --     (sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
-- --             λ f g → cong ∣_∣₂ (funExt λ x → Kn→ΩKn+1-hom n (f x) (g x)))

-- -- module lockedKnIso (key : Unit') where
-- --   Kn→ΩKn+1' : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
-- --   Kn→ΩKn+1' n = lock key (Iso.fun (Iso-Kn-ΩKn+1 n))

-- --   ΩKn+1→Kn' : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
-- --   ΩKn+1→Kn' n = lock key (Iso.inv (Iso-Kn-ΩKn+1 n))

-- --   ΩKn+1→Kn→ΩKn+1 : (n : ℕ) → (x : typ (Ω (coHomK-ptd (suc n)))) → Kn→ΩKn+1' n (ΩKn+1→Kn' n x) ≡ x
-- --   ΩKn+1→Kn→ΩKn+1 n x = pm key
-- --     where
-- --     pm : (key : Unit') → lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) (lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) x) ≡ x
-- --     pm unlock = Iso.rightInv (Iso-Kn-ΩKn+1 n) x

-- --   Kn→ΩKn+1→Kn : (n : ℕ) → (x : coHomK n) → ΩKn+1→Kn' n (Kn→ΩKn+1' n x) ≡ x
-- --   Kn→ΩKn+1→Kn n x = pm key
-- --     where
-- --     pm : (key : Unit') → lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) (lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) x) ≡ x
-- --     pm unlock = Iso.leftInv (Iso-Kn-ΩKn+1 n) x

-- -- -distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
-- --               (x y : coHom n A)
-- --             → fst f (x -[ n ]ₕ y) ≡ fst f x -[ m ]ₕ fst f y
-- -- -distrLemma n m f' x y = sym (-cancelRₕ m (f y) (f (x -[ n ]ₕ y)))
-- --                      ∙∙ cong (λ x → x -[ m ]ₕ f y) (sym (f' .snd .pres· (x -[ n ]ₕ y) y))
-- --                      ∙∙ cong (λ x → x -[ m ]ₕ f y) ( cong f (-+cancelₕ n _ _))
-- --   where
-- --   f = fst f'

-- -- -- HLevel stuff for cup product
-- -- isContr-↓∙ : (n : ℕ) → isContr (coHomK-ptd (suc n) →∙ coHomK-ptd n)
-- -- fst (isContr-↓∙ zero) = (λ _ → 0) , refl
-- -- snd (isContr-↓∙ zero) (f , p) =
-- --   Σ≡Prop (λ f → isSetℤ _ _)
-- --          (funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 isSetℤ) _ _)
-- --                  (toPropElim (λ _ → isSetℤ _ _) (sym p))))
-- -- fst (isContr-↓∙ (suc n)) = (λ _ → 0ₖ _) , refl
-- -- fst (snd (isContr-↓∙ (suc n)) f i) x =
-- --   trElim {B = λ x → 0ₖ (suc n) ≡ fst f x}
-- --     (λ _ → isOfHLevelPath (4 + n) (isOfHLevelSuc (3 + n) (isOfHLevelTrunc (3 + n))) _ _)
-- --     (sphereElim _ (λ _ → isOfHLevelTrunc (3 + n) _ _)
-- --     (sym (snd f))) x i
-- -- snd (snd (isContr-↓∙ (suc n)) f i) j = snd f (~ i ∨ j)

-- -- isContr-↓∙' : (n : ℕ) → isContr (S₊∙ (suc n) →∙ coHomK-ptd n)
-- -- fst (isContr-↓∙' zero) = (λ _ → 0) , refl
-- -- snd (isContr-↓∙' zero) (f , p) =
-- --   Σ≡Prop (λ f → isSetℤ _ _)
-- --          (funExt (toPropElim (λ _ → isSetℤ _ _) (sym p)))
-- -- fst (isContr-↓∙' (suc n)) = (λ _ → 0ₖ _) , refl
-- -- fst (snd (isContr-↓∙' (suc n)) f i) x =
-- --   sphereElim _ {A = λ x → 0ₖ (suc n) ≡ fst f x}
-- --     (λ _ → isOfHLevelTrunc (3 + n) _ _)
-- --     (sym (snd f)) x i
-- -- snd (snd (isContr-↓∙' (suc n)) f i) j = snd f (~ i ∨ j)

-- -- isOfHLevel→∙Kn : {A : Pointed₀} (n m : ℕ)
-- --   → isOfHLevel (suc m) (A →∙ coHomK-ptd n) → isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
-- -- isOfHLevel→∙Kn {A = A} n m hlev = step₃
-- --   where
-- --   step₁ : isOfHLevel (suc m) (A →∙ Ω (coHomK-ptd (suc n)))
-- --   step₁ =
-- --     subst (isOfHLevel (suc m))
-- --       (λ i → A →∙ ua∙ {A = Ω (coHomK-ptd (suc n))} {B = coHomK-ptd n}
-- --       (invEquiv Kn≃ΩKn+1)
-- --       (ΩKn+1→Kn-refl n) (~ i)) hlev

-- --   step₂ : isOfHLevel (suc m) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
-- --   step₂ = isOfHLevelRetractFromIso (suc m) (invIso (invIso (ΩfunExtIso _ _))) step₁

-- --   step₃ : isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
-- --   step₃ =
-- --     isOfHLevelΩ→isOfHLevel m
-- --       λ f → subst (λ x → isOfHLevel (suc m) (typ (Ω x)))
-- --                (isHomogeneous→∙ (isHomogeneousKn (suc n)) f)
-- --                 step₂

-- -- isOfHLevel↑∙ : ∀ n m → isOfHLevel (2 + n) (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + m)))
-- -- isOfHLevel↑∙ zero m = isOfHLevel→∙Kn m 0 (isContr→isProp (isContr-↓∙ m))
-- -- isOfHLevel↑∙ (suc n) m = isOfHLevel→∙Kn (suc (n + m)) (suc n) (isOfHLevel↑∙ n m)

-- -- isOfHLevel↑∙' : ∀ n m → isOfHLevel (2 + n) (S₊∙ (suc m) →∙ coHomK-ptd (suc (n + m)))
-- -- isOfHLevel↑∙' zero m = isOfHLevel→∙Kn m 0 (isContr→isProp (isContr-↓∙' m))
-- -- isOfHLevel↑∙' (suc n) m = isOfHLevel→∙Kn (suc (n + m)) (suc n) (isOfHLevel↑∙' n m)

-- -- →∙KnPath : (A : Pointed₀) (n : ℕ) → Ω (A →∙ coHomK-ptd (suc n) ∙) ≡ (A →∙ coHomK-ptd n ∙)
-- -- →∙KnPath A n =
-- --     ua∙ (isoToEquiv (ΩfunExtIso A (coHomK-ptd (suc n)))) refl
-- --   ∙ (λ i → (A →∙ Kn≃ΩKn+1∙ {n = n} (~ i) ∙))

-- -- contr∙-lem : (n m : ℕ)
-- --   → isContr (coHomK-ptd (suc n)
-- --            →∙ (coHomK-ptd (suc m)
-- --              →∙ coHomK-ptd (suc (n + m)) ∙))
-- -- fst (contr∙-lem n m) = (λ _ → (λ _ → 0ₖ _) , refl) , refl
-- -- snd (contr∙-lem n m) (f , p) = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousKn _)) (sym (funExt help))
-- --   where
-- --   help : (x : _) → (f x) ≡ ((λ _ → 0ₖ _) , refl)
-- --   help =
-- --     trElim (λ _ → isOfHLevelPath (3 + n)
-- --       (subst (λ x → isOfHLevel x (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + m)))) (λ i → suc (suc (+-comm n 1 i)))
-- --              (isOfHLevelPlus' {n = 1} (2 + n) (isOfHLevel↑∙ n m))) _ _)
-- --     (sphereElim _ (λ _ → isOfHLevel↑∙ n m _ _) p)

-- -- isOfHLevel↑∙∙ : ∀ n m l
-- --   → isOfHLevel (2 + l) (coHomK-ptd (suc n)
-- --                       →∙ (coHomK-ptd (suc m)
-- --                        →∙ coHomK-ptd (suc (suc (l + n + m))) ∙))
-- -- isOfHLevel↑∙∙ n m zero =
-- --   isOfHLevelΩ→isOfHLevel 0 λ f
-- --     → subst
-- --         isProp (cong (λ x → typ (Ω x))
-- --         (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousKn _)) f))
-- --         (isOfHLevelRetractFromIso 1 (ΩfunExtIso _ _) h)
-- --   where
-- --   h : isProp (coHomK-ptd (suc n)
-- --            →∙ (Ω (coHomK-ptd (suc m)
-- --             →∙ coHomK-ptd (suc (suc (n + m))) ∙)))
-- --   h =
-- --     subst isProp (λ i → coHomK-ptd (suc n) →∙ (→∙KnPath (coHomK-ptd (suc m)) (suc (n + m)) (~ i)))
-- --       (isContr→isProp (contr∙-lem n m))
-- -- isOfHLevel↑∙∙ n m (suc l) =
-- --   isOfHLevelΩ→isOfHLevel (suc l)
-- --     λ f →
-- --     subst
-- --         (isOfHLevel (2 + l)) (cong (λ x → typ (Ω x))
-- --         (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousKn _)) f))
-- --         (isOfHLevelRetractFromIso (2 + l) (ΩfunExtIso _ _) h)
-- --   where
-- --   h : isOfHLevel (2 + l)
-- --        (coHomK-ptd (suc n)
-- --          →∙ (Ω (coHomK-ptd (suc m)
-- --            →∙ coHomK-ptd (suc (suc (suc (l + n + m)))) ∙)))
-- --   h =
-- --     subst (isOfHLevel (2 + l))
-- --       (λ i → coHomK-ptd (suc n) →∙ →∙KnPath (coHomK-ptd (suc m)) (suc (suc (l + n + m))) (~ i))
-- --       (isOfHLevel↑∙∙ n m l)

-- -- -- Misc.
-- -- isoType→isoCohom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ)
-- --   → Iso A B
-- --   → GroupIso (coHomGr n A) (coHomGr n B)
-- -- fst (isoType→isoCohom n is) = setTruncIso (domIso is)
-- -- snd (isoType→isoCohom n is) =
-- --   makeIsGroupHom (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
-- --     (λ _ _ → refl))
