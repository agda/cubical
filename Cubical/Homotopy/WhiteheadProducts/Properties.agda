{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Join

open import Cubical.Homotopy.WhiteheadProducts.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base

open Iso
open 3x3-span


infixl 7 _·₋₁_
_·₋₁_ : ℕ → ℕ → ℕ
n ·₋₁ m = suc (suc n · suc m)



open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat.IsEven
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.List
open import Cubical.Data.Nat.Mod

data arithmExpr : Type where
  [_]' : (n : ℕ) → arithmExpr
  _+'_ _·'_ : arithmExpr → arithmExpr → arithmExpr

arithmExpr→ℕ : arithmExpr → ℕ
arithmExpr→ℕ [ x ]' = x
arithmExpr→ℕ (x +' y) = arithmExpr→ℕ x + arithmExpr→ℕ y
arithmExpr→ℕ (x ·' y) = arithmExpr→ℕ x · arithmExpr→ℕ y

-- _⊕'_ : Bool → Bool → Bool
-- x ⊕' y = not (not x ⊕ not y)

arithmExpr→Bool : arithmExpr → Bool
arithmExpr→Bool [ x ]' = isEven x
arithmExpr→Bool (x +' x₁) = not (not (arithmExpr→Bool x) ⊕ not (arithmExpr→Bool x₁))
arithmExpr→Bool (x ·' x₁) = arithmExpr→Bool x or arithmExpr→Bool x₁

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
isPropToType : (x : Bool) → isProp (toType x)
isPropToType false = isProp⊥
isPropToType true = isPropUnit

isPropPropPath : ∀ {ℓ} {A B : Type ℓ} → isProp A → isProp B → isProp (A ≡ B)
isPropPropPath a b = isOfHLevel⁺≡ₗ 0 a

toType⊕ : (x y : Bool) → toType (not (not x ⊕ not y)) ≃ (toType x ≡ toType y)
toType⊕ false false =
  propBiimpl→Equiv isPropUnit (isPropPropPath (λ()) (λ())) (λ _ → refl) λ _ → tt
toType⊕ false true =
 propBiimpl→Equiv isProp⊥ (isPropPropPath (λ()) isPropUnit) (λ())
   λ p → transport (sym p) tt
toType⊕ true false =
  propBiimpl→Equiv isProp⊥ (isPropPropPath isPropUnit (λ())) (λ())
    λ p → transport p tt
toType⊕ true true =
  propBiimpl→Equiv isPropUnit (isPropPropPath isPropUnit isPropUnit)
    (λ _ → refl) λ _ → tt

-- toTypeOr : (x y : Bool) → toType (
-- toTypeOr = ?


toTypeOrₗ : (x y : Bool) → toType x → toType (x or y)
toTypeOrₗ true y p = tt

toTypeOrᵣ : (x y : Bool) → toType y → toType (x or y)
toTypeOrᵣ false y p = p
toTypeOrᵣ true y p = tt

fromTypeOr : (x y : Bool) → toType (x or y) → toType x ⊎ toType y
fromTypeOr false true p = inr tt
fromTypeOr true y p = inl tt

isEvenArithm≡isEvenBool : (x : arithmExpr)
  → isEvenT (arithmExpr→ℕ x) ≡ toType (arithmExpr→Bool x)
isEvenArithm≡isEvenBool [ n ]' = refl
isEvenArithm≡isEvenBool (x +' x₁)
  with (evenOrOdd (arithmExpr→ℕ x)) | evenOrOdd (arithmExpr→ℕ x₁)
... | inl p | inl q =
  ua (isContr→≃Unit (even+even≡even _ _ p q , λ _ → isPropToType _ _ _))
   ∙ sym (ua (isContr→≃Unit (invEq (toType⊕ _ _)
         (ua (propBiimpl→Equiv (isPropToType _) (isPropToType _)
           (λ _ → transport (isEvenArithm≡isEvenBool x₁) q)
           λ _ →  transport (isEvenArithm≡isEvenBool x) p))
        , λ _ → isPropToType _ _ _)))
... | inl p | inr q =
  ua (uninhabEquiv (λ r → ¬evenAndOdd _ (r , (even+odd≡odd _ _ p q)))
                   λ r → ¬evenAndOdd _ (
                     (transport (sym (isEvenArithm≡isEvenBool x₁))
                       (transport ((fst (toType⊕ _ _) r))
                         (transport (isEvenArithm≡isEvenBool x) p)))
                     , q))
... | inr p | inl q =
  ua (uninhabEquiv (λ r → ¬evenAndOdd _ (r , (odd+even≡odd _ _ p q)))
                   λ r → ¬evenAndOdd _
                     (transport (sym (isEvenArithm≡isEvenBool x))
                      (transport (sym (fst (toType⊕ _ _) r))
                        (transport (isEvenArithm≡isEvenBool x₁) q))
                    , p))
... | inr p | inr q =
  ua (isContr→≃Unit (odd+odd≡even _ _ p q , λ _ → isPropToType _ _ _))
   ∙ sym (ua (isContr→≃Unit (invEq (toType⊕ _ _)
         (ua (propBiimpl→Equiv (isPropToType _) (isPropToType _)
           (λ r → ⊥.rec (¬evenAndOdd _
                           (transport (sym (isEvenArithm≡isEvenBool x)) r , p)))
           λ x → ⊥.rec (¬evenAndOdd _
                           (transport (sym (isEvenArithm≡isEvenBool x₁)) x , q))))
        , λ _ → isPropToType _ _ _)))
isEvenArithm≡isEvenBool (x ·' x₁)
  with (evenOrOdd (arithmExpr→ℕ x)) | evenOrOdd (arithmExpr→ℕ x₁)
... | inl p | t = ua (isContr→≃Unit
                       (even·x≡even _ _ p , λ _ → isPropToType _ _ _))
                ∙ sym (ua (isContr→≃Unit
                      (toTypeOrₗ _ _ (transport (isEvenArithm≡isEvenBool x) p)
                  , λ _ → isPropToType _ _ _)))
... | inr p | inl q =
  ua (isContr→≃Unit (x·even≡even _ _ q , λ _ → isPropToType _ _ _))
  ∙ sym (ua (isContr→≃Unit (toTypeOrᵣ _ _ (transport (isEvenArithm≡isEvenBool x₁) q)
                           , λ _ → isPropToType _ _ _)))
... | inr p | inr q =
  ua (uninhabEquiv
   (λ r → ¬evenAndOdd _ (r , (odd·odd≡odd _ _ p q)))
   λ r → ¬evenAndOdd _
     (⊎.rec (λ r → even·x≡even _ _
                    (transport (sym (isEvenArithm≡isEvenBool x)) r))
            (λ r → x·even≡even _ _
                    (transport (sym (isEvenArithm≡isEvenBool x₁)) r))
            (fromTypeOr _ _ r) , odd·odd≡odd _ _ p q) )

⊕comm : (a b : Bool) → a ⊕ b ≡ b ⊕ a
⊕comm false false = refl
⊕comm false true = refl
⊕comm true false = refl
⊕comm true true = refl

even⊕odd : (r : _) → toType (isEven r ⊕ isOdd r)
even⊕odd zero = tt
even⊕odd (suc r) = subst toType (⊕comm _ _) (even⊕odd r)

even≡oddFlip : (n m : ℕ) → isEvenT n ≡ isOddT m → isOddT n ≡ isEvenT m
even≡oddFlip zero zero p = sym p
even≡oddFlip zero (suc zero) p = refl
even≡oddFlip zero (suc (suc m)) p = even≡oddFlip zero m p
even≡oddFlip (suc zero) zero p = refl
even≡oddFlip (suc zero) (suc zero) p = sym p
even≡oddFlip (suc zero) (suc (suc m)) p = even≡oddFlip (suc zero) m p
even≡oddFlip (suc (suc n)) m p = even≡oddFlip n m p

evenOddLemma1' : (p q r : ℕ)
  → isEvenT (p ·₋₁ r + r ·₋₁ (p + suc q)) ≡ isOddT (r ·₋₁ q)
evenOddLemma1' p q r =
    isEvenArithm≡isEvenBool expr
  ∙ main (even⊕odd r) (even⊕odd p)
  ∙ sym (isEvenArithm≡isEvenBool expr2)
  where
  expr expr2 : arithmExpr
  expr = ((([ r ]' +' ([ p ]' ·' [ suc r ]'))
      +' ([ 2 ]' +' (([ p ]' +' [ suc q ]')
      +' ([ r ]' ·' ([ suc p ]' +' [ suc q ]'))))))
  expr2 = ([ suc r ]' ·' [ suc q ]')

  main : toType (isEven r ⊕ isOdd r) → toType (isEven p ⊕ isOdd p)
       → toType (arithmExpr→Bool expr) ≡ toType (arithmExpr→Bool expr2)
  main t s with (isEven r) | (isOdd r) | (isEven p) | (isOdd p) | (isOdd q)
  ... | true | false | false | d | false = refl
  ... | true | false | true | d | false = refl
  ... | true | false | false | d | true = refl
  ... | true | false | true | d | true = refl
  ... | false | true | false | true | false = refl
  ... | false | true | false | true | true = refl
  ... | false | true | true | false | false = refl
  ... | false | true | true | false | true = refl

-- evenOddLemma1'' : (p q r : ℕ)
--   → isOddT (p ·₋₁ r + r ·₋₁ (p + suc q)) ≡ isEvenT (r ·₋₁ q)
-- evenOddLemma1'' p q r =
--     isEvenArithm≡isEvenBool expr
--   ∙ main (even⊕odd r) (even⊕odd p)
--   ∙ sym (isEvenArithm≡isEvenBool expr2)
--   where
--   expr expr2 : arithmExpr
--   expr = [ 1 ]' +' ((([ r ]' +' ([ p ]' ·' [ suc r ]'))
--       +' ([ 2 ]' +' (([ p ]' +' [ suc q ]')
--       +' ([ r ]' ·' ([ suc p ]' +' [ suc q ]'))))))
--   expr2 = [ 1 ]' +' ([ suc r ]' ·' [ suc q ]')

--   main : toType (isEven r ⊕ isOdd r) → toType (isEven p ⊕ isOdd p)
--        → toType (arithmExpr→Bool expr) ≡ toType (arithmExpr→Bool expr2)
--   main t s with (isEven r) | (isOdd r) | (isEven p) | (isOdd p) | (isOdd q)
--   ... | true | false | false | d | false = refl
--   ... | true | false | true | d | false = refl
--   ... | true | false | false | d | true = refl
--   ... | true | false | true | d | true = refl
--   ... | false | true | false | true | false = refl
--   ... | false | true | false | true | true = refl
--   ... | false | true | true | false | false = refl
--   ... | false | true | true | false | true = refl

-- evenOddLemma1 : (p q r : ℕ)
--   → (isEvenT (p ·₋₁ r + r ·₋₁ (p + suc q)) → isOddT (r ·₋₁ q))
-- evenOddLemma1 p q r t with (evenOrOdd p) | evenOrOdd q | evenOrOdd r
-- ... | evp | inl evq | inl evr =
--   ⊥.rec (¬evenAndOdd _ (t
--         , subst isOddT (+-comm (suc (suc (p + suc q + r · suc (p + suc q))))
--                                (r + p · suc r))
--           lem))
--   where
--   lem : isOddT (p + suc q + r · suc (p + suc q) + (r + p · suc r))
--   lem = subst isOddT
--     (+-assoc r (p · suc r) (p + suc q + r · suc (p + suc q))
--     ∙ +-comm (r + p · suc r) (p + suc q + r · suc (p + suc q)))
--     (even+odd≡odd r (p · suc r + (p + suc q + r · suc (p + suc q)))
--       evr
--       (subst isOddT
--         (sym (+-assoc (p · suc r) (p + suc q) (r · suc (p + suc q))))
--         (odd+even≡odd _ (r · suc (p + suc q))
--           (subst isOddT (sym (+-assoc (p · suc r) p (suc q)))
--             (even+odd≡odd (p · suc r + p) (suc q)
--               (subst isEvenT (cong (p +_) (·-comm (suc r) p)
--                 ∙ sym (+-comm (p · suc r) p))
--                 (even·x≡even (suc (suc r)) p evr)) evq))
--           (even·x≡even r (suc p + suc q) evr))))
-- ... | evp | inr odq | inl evr =
--   transport (λ i → isEvenT (suc r · suc q))
--   (x·even≡even (suc r) (suc q) odq)
-- ... | evp | evq | inr odr = transport (λ i → isEvenT (suc r · suc q))
--   (even·x≡even (suc r) (suc q) odr)

-- evenOddLemma2 : (p q r : ℕ)
--   → (isOddT (p ·₋₁ r + r ·₋₁ (p + suc q)) → isEvenT (r ·₋₁ q))
-- evenOddLemma2 p q r t with (evenOrOdd p) | evenOrOdd q | evenOrOdd r
-- ... | evp | evq | evr = {!!}


[]comp≡[] : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (f : (S₊∙ (suc n) →∙ X))
       → (g : (S₊∙ (suc m) →∙ X))
       → [ f ∣ g ]comp ≡ [ f ∣ g ]
[]comp≡[] {X = X} {n = n} {m} f g =
  cong (_∘∙ (sphere→Join n m , IsoSphereJoin⁻Pres∙ n m)) (main n m f g)
    where
    ∨fun : {n m : ℕ} (f : (S₊∙ (suc n) →∙ X)) (g : (S₊∙ (suc m) →∙ X))
      → ((_ , inl north) →∙ X)
    ∨fun {n = n} {m} f g =
       ((f ∘∙ (inv (IsoSucSphereSusp n) , IsoSucSphereSusp∙ n)) ∨→
       (g ∘∙ (inv (IsoSucSphereSusp m) , IsoSucSphereSusp∙ m))
       , cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f)

    main : (n m : ℕ) (f : (S₊∙ (suc n) →∙ X)) (g : (S₊∙ (suc m) →∙ X))
      → (∨fun f g ∘∙ (joinTo⋁ {A = S₊∙ n} {B = S₊∙ m} , sym (push tt)))
      ≡ [ f ∣ g ]-pre
    main n m f g =
      ΣPathP ((funExt (λ { (inl x) → rp
                         ; (inr x) → lp
                         ; (push a b i) j → pushcase a b j i}))
          , ((cong₂ _∙_ (symDistr _ _) refl
          ∙ sym (assoc _ _ _)
          ∙ cong (rp ∙_) (rCancel _)
          ∙ sym (rUnit rp))
          ◁ λ i j → rp (i ∨ j)))
      where
      lp = cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f
      rp = cong (fst g) (IsoSucSphereSusp∙ m) ∙ snd g

      help : (n : ℕ) (a : _)
        → Square (cong (inv (IsoSucSphereSusp n)) (σ (S₊∙ n) a)) (σS a)
                  (IsoSucSphereSusp∙ n) (IsoSucSphereSusp∙ n)
      help zero a = cong-∙ SuspBool→S¹ (merid a) (sym (merid (pt (S₊∙ zero))))
                  ∙ sym (rUnit _)
      help (suc n) a = refl

      ∙∙Distr∙ : ∀ {ℓ} {A : Type ℓ} {x y z w u : A}
                 {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} {s : w ≡ u}
               → p ∙∙ q ∙ r ∙∙ s ≡ ((p ∙ q) ∙ r ∙ s)
      ∙∙Distr∙ = doubleCompPath≡compPath _ _ _
               ∙ assoc _ _ _
               ∙ cong₂ _∙_ (assoc _ _ _) refl
               ∙ sym (assoc _ _ _)

      pushcase : (a : S₊ n) (b : S₊ m)
        → Square (cong (∨fun f g .fst
                       ∘ joinTo⋁ {A = S₊∙ n} {B = S₊∙ m}) (push a b))
                  (cong (fst [ f ∣ g ]-pre) (push a b))
                  rp lp
      pushcase a b =
        (cong-∙∙ (∨fun f g .fst) _ _ _
        ∙ (λ i → cong (fst g) (PathP→compPathR∙∙ (help _ b) i)
              ∙∙ symDistr lp (sym rp) i
              ∙∙ cong (fst f) (PathP→compPathR∙∙ (help _ a) i))
        ∙ (λ i → cong (fst g)
                      (IsoSucSphereSusp∙ m
                     ∙∙ σS b
                     ∙∙ (λ j → IsoSucSphereSusp∙ m (~ j ∨ i)))
              ∙∙ compPath-filler' (cong (fst g) (IsoSucSphereSusp∙ m)) (snd g) (~ i)
               ∙ sym (compPath-filler' (cong (fst f) (IsoSucSphereSusp∙ n)) (snd f) (~ i))
              ∙∙ cong (fst f)
                      ((λ j → IsoSucSphereSusp∙ n (i ∨ j))
                      ∙∙ σS a
                      ∙∙ sym (IsoSucSphereSusp∙ n))))
       ◁ compPathR→PathP∙∙
           ( ∙∙Distr∙
          ∙ cong₂ _∙_ (cong₂ _∙_ (cong (cong (fst g)) (sym (compPath≡compPath' _ _)))
                                 refl)
                      refl
          ∙ cong₂ _∙_ (cong (_∙ snd g) (cong-∙ (fst g) (IsoSucSphereSusp∙ m) (σS b))
                                     ∙ sym (assoc _ _ _))
                      (cong (sym (snd f) ∙_)
                        (cong-∙ (fst f) (σS a)
                          (sym (IsoSucSphereSusp∙ n)))
                         ∙ assoc _ _ _)
          ∙ sym ∙∙Distr∙
          ∙ cong₃ _∙∙_∙∙_ refl (cong₂ _∙_ refl (compPath≡compPath' _ _)) refl
         ∙ λ i → compPath-filler (cong (fst g) (IsoSucSphereSusp∙ m)) (snd g) i
               ∙∙ ((λ j → snd g (~ j ∧ i)) ∙∙ cong (fst g) (σS b) ∙∙ snd g)
                ∙ (sym (snd f) ∙∙ cong (fst f) (σS a) ∙∙ λ j → snd f (j ∧ i))
               ∙∙ sym (compPath-filler (cong (fst f) (IsoSucSphereSusp∙ n)) (snd f) i))

-- We prove that the function joinTo⋁ used in the definition of the whitehead
-- product gives an equivalence between (Susp A × Susp B) and the
-- appropriate cofibre of joinTo⋁ (last two theorems in the following
-- module).

module _ (A B : Type) (a₀ : A) (b₀ : B) where
  private
    W = joinTo⋁ {A = (A , a₀)} {B = (B , b₀)}

  A∨B = (Susp A , north) ⋁ (Susp B , north)

  σB = σ (B , b₀)
  σA = σ (A , a₀)

  cofibW = Pushout W λ _ → tt

  whitehead3x3 :  3x3-span
  A00 whitehead3x3 = Susp A
  A02 whitehead3x3 = B
  A04 whitehead3x3 = Unit
  A20 whitehead3x3 = B
  A22 whitehead3x3 = A × B
  A24 whitehead3x3 = A
  A40 whitehead3x3 = B
  A42 whitehead3x3 = B
  A44 whitehead3x3 = Unit
  f10 whitehead3x3 _ = south
  f12 whitehead3x3 = snd
  f14 whitehead3x3 _ = tt
  f30 whitehead3x3 = idfun B
  f32 whitehead3x3 = snd
  f34 whitehead3x3 _ = tt
  f01 whitehead3x3 _ = north
  f21 whitehead3x3 = snd
  f41 whitehead3x3 = idfun B
  f03 whitehead3x3 _ = tt
  f23 whitehead3x3 = fst
  f43 whitehead3x3 _ = tt
  H11 whitehead3x3 x = merid (fst x)
  H13 whitehead3x3 _ = refl
  H31 whitehead3x3 _ = refl
  H33 whitehead3x3 _ = refl

  A0□→A∨B : A0□ whitehead3x3 → A∨B
  A0□→A∨B (inl x) = inl x
  A0□→A∨B (inr x) = inr north
  A0□→A∨B (push a i) = (push tt ∙ λ i → inr (σB a (~ i))) i

  A∨B→A0□ : A∨B → A0□ whitehead3x3
  A∨B→A0□ (inl x) = inl x
  A∨B→A0□ (inr north) = inl north
  A∨B→A0□ (inr south) = inl north
  A∨B→A0□ (inr (merid b i)) = (push b₀ ∙ sym (push b)) i
  A∨B→A0□ (push a i) = inl north

  Iso-A0□-⋁ : Iso (A0□ whitehead3x3) A∨B
  fun Iso-A0□-⋁ = A0□→A∨B
  inv Iso-A0□-⋁ = A∨B→A0□
  rightInv Iso-A0□-⋁ (inl x) = refl
  rightInv Iso-A0□-⋁ (inr north) = push tt
  rightInv Iso-A0□-⋁ (inr south) = push tt ∙ λ i → inr (merid b₀ i)
  rightInv Iso-A0□-⋁ (inr (merid a i)) j = lem j i
    where
    lem : PathP (λ i → push tt i ≡ (push tt ∙ (λ i → inr (merid b₀ i))) i)
              (cong A0□→A∨B (cong A∨B→A0□ λ i → inr (merid a i)))
              (λ i → inr (merid a i))
    lem = (cong-∙ A0□→A∨B (push b₀) (sym (push a))
      ∙ cong₂ _∙_ (cong (push tt ∙_)
                  (λ j i → inr (rCancel (merid b₀) j (~ i)))
                 ∙ sym (rUnit (push tt)))
                  (symDistr (push tt) (λ i → inr (σB a (~ i)))))
      ◁ λ i j → hcomp (λ k →
                  λ { (i = i0) → compPath-filler' (push tt)
                                 (compPath-filler (λ i → inr (σB a i))
                                                  (sym (push tt)) k) k j
                    ; (i = i1) → inr (merid a j)
                    ; (j = i0) → push tt (i ∨ ~ k)
                    ; (j = i1) → compPath-filler' (push tt)
                                                  (λ i → inr (merid b₀ i)) k i})
                        (inr (compPath-filler (merid a)
                                              (sym (merid b₀)) (~ i) j))

  rightInv Iso-A0□-⋁ (push a i) j = push tt (i ∧ j)
  leftInv Iso-A0□-⋁ (inl x) = refl
  leftInv Iso-A0□-⋁ (inr tt) = push b₀
  leftInv Iso-A0□-⋁ (push b i) j = help j i
    where
    help : PathP (λ i → inl north ≡ push b₀ i)
                 (cong A∨B→A0□ (cong A0□→A∨B (push b)))
                 (push b)
    help = (cong-∙ A∨B→A0□ (push tt) (λ i → inr (σB b (~ i)))
         ∙ (λ i → lUnit (sym (cong-∙ (A∨B→A0□ ∘ inr)
                               (merid b) (sym (merid b₀)) i)) (~ i))
         ∙ cong sym (cong ((push b₀ ∙ sym (push b)) ∙_)
                      (cong sym (rCancel (push b₀))))
         ∙ cong sym (sym (rUnit (push b₀ ∙ sym (push b)))))
         ◁ λ i j → compPath-filler' (push b₀) (sym (push b)) (~ i) (~ j)

  Iso-A2□-join : Iso (A2□ whitehead3x3) (join A B)
  fun Iso-A2□-join (inl x) = inr x
  fun Iso-A2□-join (inr x) = inl x
  fun Iso-A2□-join (push (a , b) i) = push a b (~ i)
  inv Iso-A2□-join (inl x) = inr x
  inv Iso-A2□-join (inr x) = inl x
  inv Iso-A2□-join (push a b i) = push (a , b) (~ i)
  rightInv Iso-A2□-join (inl x) = refl
  rightInv Iso-A2□-join (inr x) = refl
  rightInv Iso-A2□-join (push a b i) = refl
  leftInv Iso-A2□-join (inl x) = refl
  leftInv Iso-A2□-join (inr x) = refl
  leftInv Iso-A2□-join (push a i) = refl

  isContrA4□ : isContr (A4□ whitehead3x3)
  fst isContrA4□ = inr tt
  snd isContrA4□ (inl x) = sym (push x)
  snd isContrA4□ (inr x) = refl
  snd isContrA4□ (push a i) j = push a (i ∨ ~ j)

  A4□≃Unit : A4□ whitehead3x3 ≃ Unit
  A4□≃Unit = isContr→≃Unit isContrA4□

  Iso-A□0-Susp : Iso (A□0 whitehead3x3) (Susp A)
  fun Iso-A□0-Susp (inl x) = x
  fun Iso-A□0-Susp (inr x) = north
  fun Iso-A□0-Susp (push a i) = merid a₀ (~ i)
  inv Iso-A□0-Susp x = inl x
  rightInv Iso-A□0-Susp x = refl
  leftInv Iso-A□0-Susp (inl x) = refl
  leftInv Iso-A□0-Susp (inr x) = (λ i → inl (merid a₀ i)) ∙ push x
  leftInv Iso-A□0-Susp (push a i) j =
    hcomp (λ k → λ { (i = i0) → inl (merid a₀ (k ∨ j))
                    ; (i = i1) → compPath-filler
                                   (λ i₁ → inl (merid a₀ i₁))
                                   (push (idfun B a)) k j
                    ; (j = i0) → inl (merid a₀ (~ i ∧ k))
                    ; (j = i1) → push a (i ∧ k)})
          (inl (merid a₀ j))

  Iso-A□2-Susp× : Iso (A□2 whitehead3x3) (Susp A × B)
  fun Iso-A□2-Susp× (inl x) = north , x
  fun Iso-A□2-Susp× (inr x) = south , x
  fun Iso-A□2-Susp× (push a i) = merid (fst a) i , (snd a)
  inv Iso-A□2-Susp× (north , y) = inl y
  inv Iso-A□2-Susp× (south , y) = inr y
  inv Iso-A□2-Susp× (merid a i , y) = push (a , y) i
  rightInv Iso-A□2-Susp× (north , snd₁) = refl
  rightInv Iso-A□2-Susp× (south , snd₁) = refl
  rightInv Iso-A□2-Susp× (merid a i , snd₁) = refl
  leftInv Iso-A□2-Susp× (inl x) = refl
  leftInv Iso-A□2-Susp× (inr x) = refl
  leftInv Iso-A□2-Susp× (push a i) = refl

  Iso-A□4-Susp : Iso (A□4 whitehead3x3) (Susp A)
  fun Iso-A□4-Susp (inl x) = north
  fun Iso-A□4-Susp (inr x) = south
  fun Iso-A□4-Susp (push a i) = merid a i
  inv Iso-A□4-Susp north = inl tt
  inv Iso-A□4-Susp south = inr tt
  inv Iso-A□4-Susp (merid a i) = push a i
  rightInv Iso-A□4-Susp north = refl
  rightInv Iso-A□4-Susp south = refl
  rightInv Iso-A□4-Susp (merid a i) = refl
  leftInv Iso-A□4-Susp (inl x) = refl
  leftInv Iso-A□4-Susp (inr x) = refl
  leftInv Iso-A□4-Susp (push a i) = refl

  Iso-PushSusp×-Susp×Susp :
    Iso (Pushout {A = Susp A × B} fst fst) (Susp A × Susp B)
  Iso-PushSusp×-Susp×Susp = theIso
    where
    F : Pushout {A = Susp A × B} fst fst
     → Susp A × Susp B
    F (inl x) = x , north
    F (inr x) = x , north
    F (push (x , b) i) = x , σB b i

    G : Susp A × Susp B → Pushout {A = Susp A × B} fst fst
    G (a , north) = inl a
    G (a , south) = inr a
    G (a , merid b i) = push (a , b) i

    retr : retract F G
    retr (inl x) = refl
    retr (inr x) = push (x , b₀)
    retr (push (a , b) i) j = help j i
      where
      help : PathP (λ i → Path (Pushout fst fst) (inl a) (push (a , b₀) i))
                   (cong G (λ i → a , σB b i))
                   (push (a , b))
      help = cong-∙ (λ x → G (a , x)) (merid b) (sym (merid b₀))
                  ◁ λ i j → compPath-filler
                               (push (a , b))
                               (sym (push (a , b₀)))
                               (~ i) j

    theIso : Iso (Pushout fst fst) (Susp A × Susp B)
    fun theIso = F
    inv theIso = G
    rightInv theIso (a , north) = refl
    rightInv theIso (a , south) = ΣPathP (refl , merid b₀)
    rightInv theIso (a , merid b i) j =
      a , compPath-filler (merid b) (sym (merid b₀)) (~ j) i
    leftInv theIso = retr

  Iso-A□○-PushSusp× :
    Iso (A□○ whitehead3x3) (Pushout {A = Susp A × B} fst fst)
  Iso-A□○-PushSusp× =
    pushoutIso _ _ fst fst
      (isoToEquiv Iso-A□2-Susp×)
      (isoToEquiv Iso-A□0-Susp)
      (isoToEquiv Iso-A□4-Susp)
      (funExt (λ { (inl x) → refl
                 ; (inr x) → merid a₀
                 ; (push a i) j → help₁ a j i}))
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push a i) j
                  → fun Iso-A□4-Susp (rUnit (push (fst a)) (~ j) i)})
    where
    help₁ : (a : A × B)
      → PathP (λ i → north ≡ merid a₀ i)
               (cong (fun Iso-A□0-Susp)
                 (cong (f□1 whitehead3x3) (push a)))
               (merid (fst a))
    help₁ a =
        (cong-∙∙ (fun Iso-A□0-Susp)
                 (λ i → inl (merid (fst a) i))
                 (push (snd a))
                 refl)
      ◁ (λ i j → hcomp (λ k → λ {(i = i1) → merid (fst a) (j ∨ ~ k)
                                 ; (j = i0) → merid (fst a) (~ k)
                                 ; (j = i1) → merid a₀ i})
                        (merid a₀ (i ∨ ~ j)))

  Iso-A□○-Susp×Susp : Iso (A□○ whitehead3x3) (Susp A × Susp B)
  Iso-A□○-Susp×Susp = compIso Iso-A□○-PushSusp× Iso-PushSusp×-Susp×Susp

  Iso-A○□-cofibW : Iso (A○□ whitehead3x3) cofibW
  Iso-A○□-cofibW =
    pushoutIso _ _
      W (λ _ → tt)
      (isoToEquiv Iso-A2□-join) (isoToEquiv Iso-A0□-⋁)
      A4□≃Unit
      (funExt lem)
      λ _ _ → tt
    where
    lem : (x : A2□ whitehead3x3)
      → A0□→A∨B (f1□ whitehead3x3 x) ≡ W (fun Iso-A2□-join x)
    lem (inl x) = (λ i → inl (merid a₀ (~ i)))
    lem (inr x) = refl
    lem (push (a , b) i) j = help j i
      where
      help : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
                                ((inl (merid a₀ (~ i))))
                                (inr north))
                   (cong A0□→A∨B (cong (f1□ whitehead3x3) (push (a , b))))
                   (cong W (cong (fun Iso-A2□-join) (push (a , b))))
      help = (cong-∙∙ A0□→A∨B (λ i → inl (merid a (~ i))) (push b) refl
            ∙ λ j → (λ i₂ → inl (merid a (~ i₂)))
                   ∙∙ compPath-filler (push tt) (λ i → inr (σB b (~ i))) (~ j)
                   ∙∙ λ i → inr (σB b (~ i ∧ j)))
           ◁ (λ j → (λ i → inl (sym (compPath-filler
                                       (merid a) (sym (merid a₀)) j) i))
                   ∙∙ push tt
                   ∙∙ λ i → inr (σB b (~ i)))

  Iso₁-Susp×Susp-cofibW : Iso (Susp A × Susp B) cofibW
  Iso₁-Susp×Susp-cofibW =
    compIso (invIso Iso-A□○-Susp×Susp)
            (compIso (3x3-Iso whitehead3x3) Iso-A○□-cofibW)

  -- Main iso
  Iso-Susp×Susp-cofibJoinTo⋁ : Iso (Susp A × Susp B) cofibW
  Iso-Susp×Susp-cofibJoinTo⋁ =
    compIso (Σ-cong-iso-snd (λ _ → invSuspIso))
            Iso₁-Susp×Susp-cofibW

  -- The induced function A ∨ B → Susp A × Susp B satisfies
  -- the following identity
  Susp×Susp→cofibW≡ : Path (A∨B → Susp A × Susp B)
                      (Iso.inv Iso-Susp×Susp-cofibJoinTo⋁ ∘ inl)
                      ⋁↪
  Susp×Susp→cofibW≡ =
    funExt λ { (inl x) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr north) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr south) → refl
             ; (inr (merid a i)) j → lem₂ a j i
             ; (push a i) j → north , (merid b₀ (~ j))}
    where
    f₁ = fun Iso-PushSusp×-Susp×Susp
    f₂ = fun Iso-A□○-PushSusp×
    f₃ = backward-l whitehead3x3
    f₄ = fun (Σ-cong-iso-snd (λ _ → invSuspIso))

    lem : (b : B)
      → cong (f₁ ∘ f₂ ∘ f₃) (push b)
      ≡ (λ i → north , σB b i)
    lem b = cong (cong f₁) (sym (rUnit (push (north , b))))

    lem₂ : (a : B)
      → PathP (λ i → (north , merid b₀ (~ i)) ≡ (north , south))
               (cong (f₄ ∘ f₁ ∘ f₂ ∘ f₃ ∘ A∨B→A0□ ∘ inr) (merid a))
               λ i → north , merid a i
    lem₂ a =
         cong (cong f₄) (cong-∙ (f₁ ∘ f₂ ∘ f₃) (push b₀) (sym (push a))
      ∙∙ cong₂ _∙_ (lem b₀ ∙ (λ j i → north , rCancel (merid b₀) j i))
                   (cong sym (lem a))
      ∙∙ sym (lUnit (λ i₁ → north , σB a (~ i₁))))
       ∙ (λ i j → north , cong-∙ invSusp (merid a) (sym (merid b₀)) i (~ j) )
        ◁ λ i j → north , compPath-filler (sym (merid a)) (merid b₀) (~ i) (~ j)


open import Cubical.Data.Nat.Order

open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base hiding (·wh)
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Properties
open import Cubical.Homotopy.Group.Join
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Bool hiding (_≤_)
invSpherePt : {k : ℕ} → invSphere (ptSn (suc k)) ≡ ptSn (suc k)
invSpherePt {k = zero} = refl
invSpherePt {k = suc k} = sym (merid (ptSn (suc k)))

invSphere∙ : {k : ℕ} → S₊∙ (suc k) →∙ S₊∙ (suc k)
invSphere∙ {k = k} .fst = invSphere
invSphere∙ {k = k} .snd = invSpherePt

invSphere∙² : {k : ℕ} → invSphere∙ {k = k} ∘∙ invSphere∙ {k = k} ≡ idfun∙ (S₊∙ (suc k))
invSphere∙² {k = k} i .fst x = invSphere² _ x i
invSphere∙² {k = zero} i .snd j = rUnit (λ _ → ptSn 1) (~ i) j
invSphere∙² {k = suc k} i .snd j = rCancel (merid (ptSn (suc k))) i j

-S^pt : {k : ℕ} (n : ℕ) → -S^ {k = suc k} n (ptSn (suc k)) ≡ ptSn (suc k)
-S^pt {k = k} n = iter∙ n (invSphere , invSpherePt) .snd

-S^∙ : {k : ℕ} (n : ℕ) → S₊∙ (suc k) →∙ S₊∙ (suc k)
-S^∙ n .fst = -S^ n
-S^∙ n .snd = -S^pt n

-S^∙+1 : {k : ℕ} (n : ℕ)
  → (-S^∙ {k = k} 1 ∘∙ -S^∙ {k = k} (suc n)) ≡ -S^∙ {k = k} n
-S^∙+1 {k = k} n i .fst x = invSphere² _ (-S^ n x) i
-S^∙+1 {k = k} n i .snd j =
  hcomp (λ r →
      λ{(i = i1) → invSphere² (suc k) (-S^pt n j) r
      ; (j = i0) → invSphere² (suc k) (-S^ n (S₊∙ (suc k) .snd)) (i ∧ r)
      ; (j = i1) → lem k i r
      })
      (-S^ 1 (compPath-filler (λ i₁ → invSphere (-S^pt n i₁)) invSpherePt (~ i) j))
  where
  lem : (k : ℕ)
    → Square (refl ∙ invSpherePt)
             (invSphere² (suc k) (ptSn (suc k)))
             (cong invSphere (sym (invSpherePt {k = k}))) refl
  lem zero = sym (lUnit refl)
  lem (suc k) = sym (lUnit _) ◁ λ i j → merid (ptSn (suc k)) (~ i ∧ ~ j)


suspFun∙Comp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (g : B → C) (f : A → B) → suspFun∙ (g ∘ f) ≡ (suspFun∙ g ∘∙ suspFun∙ f)
suspFun∙Comp f g = ΣPathP ((suspFunComp f g) , rUnit refl)

suspFun∙idfun : ∀ {ℓ} {A : Type ℓ}
  → suspFun∙ (idfun A) ≡ idfun∙ _
suspFun∙idfun = ΣPathP (suspFunIdFun , refl)

private
  -S^∙suspFun₁ : {k : ℕ} → -S^∙ {k = suc k} 1 ≡ suspFun∙ (-S^ {k = suc k} 1)
  -S^∙suspFun₁ {k = k} =
    ΣPathP ((funExt λ { north → sym (merid (ptSn (suc k)))
                      ; south → merid (ptSn (suc k))
                      ; (merid a i) k → lem a k i})
                      , (sym (lUnit _)
                      ◁ λ i j → merid (ptSn (suc k)) (~ j ∧ ~ i)))
    where
    lem : (a : S₊ (suc k))
      → Square (sym (merid a)) (merid (invSphere a))
                (sym (merid (ptSn (suc k)))) (merid (ptSn (suc k)))
    lem a =
       (λ i → compPath-filler
                 (sym (compPath-filler (merid a)
                        (sym (merid (ptSn (suc k)))) i))
                 (merid (ptSn (suc k))) i)
      ▷ (refl
      ∙ cong (_∙ merid (ptSn (suc k))) (sym (σ-invSphere _ a))
      ∙ sym (assoc _ _ _)
      ∙ cong₂ _∙_ refl (lCancel _)
      ∙ sym (rUnit _))

-S^∙suspFun : {k : ℕ} (n : ℕ) → -S^∙ {k = suc k} n ≡ suspFun∙ (-S^ {k = suc k} n)
-S^∙suspFun zero = ΣPathP (sym suspFunIdFun , refl)
-S^∙suspFun (suc n) =
    ΣPathP (refl , cong₂ _∙_ refl (lUnit _))
  ∙ cong₂ _∘∙_ -S^∙suspFun₁ (-S^∙suspFun n)
  ∙ sym (suspFun∙Comp (-S^ 1) (-S^ n))

-π^ : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ) → π' (suc k) A → π' (suc k) A
-π^ {k = k} n = iter n (-π' k)

-π^≡iter-Π : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ)
  → (x : π' (suc k) A) → -π^ n x ≡ ST.map (iter n -Π) x
-π^≡iter-Π {k = k} zero = ST.elim (λ _ → isSetPathImplicit) λ _ → refl
-π^≡iter-Π {k = k} (suc n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong (-π^ 1) (-π^≡iter-Π {k = k} n ∣ f ∣₂)

open import Cubical.HITs.S1 hiding (_·_)

-Π≡∘-S : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (f : S₊∙ (suc k) →∙ A)
  → -Π f ≡ (f ∘∙ (invSphere , invSpherePt))
-Π≡∘-S {k = zero} {A} f =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) → refl}))
        , lUnit (snd f))
-Π≡∘-S {k = suc k} {A} f =
  ΣPathP ((funExt (λ { north → cong (fst f) (merid (ptSn (suc k)))
                     ; south → refl
                     ; (merid a i) j
                  → fst f (compPath-filler (merid a)
                            (sym (merid (ptSn (suc k)))) (~ j) (~ i))}))
        , (compPath-filler'
             (cong (fst f) (sym (merid (ptSn (suc k)))))
             (snd f)))

iter-Π≡∘-S^ : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ) (f : S₊∙ (suc k) →∙ A)
  → iter n -Π f ≡ (f ∘∙ (-S^ n , -S^pt n))
iter-Π≡∘-S^ {k = k} {A} zero f = ΣPathP (refl , lUnit (snd f))
iter-Π≡∘-S^ {k = k} {A} (suc n) f =
  cong -Π (iter-Π≡∘-S^ {k = k} {A} n f)
  ∙ -Π≡∘-S (f ∘∙ (-S^ n , -S^pt n))
  ∙ ∘∙-assoc f (-S^ n , -S^pt n) (invSphere , invSpherePt) -- 
  ∙ cong (f ∘∙_)
    (ΣPathP ((funExt (λ x → sym (invSphere-S^ n x)))
           , (lem k n)))
  where
  fl : (k : ℕ) (n : ℕ)
    → Σ[ p ∈ invSphere (invSphere (ptSn (suc k))) ≡ ptSn (suc k) ]
    ((Square (cong invSphere (sym (invSpherePt {k = k})) )
            refl invSpherePt p)
    × Square (cong (invSphere ∘ invSphere) (-S^pt n))
             (cong invSphere (cong invSphere (-S^pt n) ∙ invSpherePt) ∙ invSpherePt)
             refl
             p)
  fl zero n .fst = refl
  fl (suc k) n .fst = refl
  fl zero n .snd = refl
    , (cong (congS invLooper) (rUnit (cong invLooper (-S^pt n))) ∙ rUnit _)
  fl (suc k) n .snd .fst i j = merid (ptSn (suc k)) (~ i ∧ ~ j)
  fl (suc k) n .snd .snd i j =
    hcomp (λ r → λ {(i = i0) → invSusp (invSusp (-S^pt n j))
                   ; (j = i0) → invSusp (invSusp (iter n invSusp north))
                   ; (j = i1) → merid (ptSn (suc k)) (~ r ∧ i)})
           (invSusp (compPath-filler (cong invSusp (-S^pt n))
                      (sym (merid (ptSn (suc k)))) i j))

  lem : (k : ℕ) (n : ℕ)
    → Square (cong (-S^ n) (invSpherePt {k = k}) ∙ -S^pt n)
              (-S^pt (suc n))
              (sym (invSphere-S^ n (ptSn (suc k)))) refl
  lem k zero = sym (rUnit _) ∙ lUnit _
  lem k (suc n) i j =
    hcomp (λ r → λ {(i = i0) → (cong (-S^ (suc n)) (invSpherePt {k = k})
                              ∙ compPath-filler (cong invSphere (-S^pt n))
                                                      invSpherePt r) j
                   ; (i = i1) → fl k n .snd .snd r j
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → fl k n .snd .fst r i
                   })
     (hcomp (λ r → λ {(i = i0) → cong-∙ invSphere
                                         (cong (-S^ n) (invSpherePt {k = k}))
                                         (-S^pt n) r j
                   ; (i = i1) → invSphere (doubleCompPath-filler refl
                                  (cong invSphere (-S^pt n)) invSpherePt (~ r) j)
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → invSphere (invSpherePt (~ r ∨ ~ i))})
          (invSphere (lem k n i j)))


open import Cubical.Data.Nat.IsEven

-S^-even : {k : ℕ} (n : ℕ) → isEvenT n → (x : S₊ (suc k)) → -S^ n x ≡ x
-S^-even zero p x = refl
-S^-even (suc (suc n)) p x =
  cong (invSphere ∘ invSphere) (-S^-even n p x)
  ∙ invSphere² _ x

-S^∙-even : {k : ℕ} (n : ℕ) → isEvenT n → -S^∙ {k = k} n ≡ idfun∙ (S₊∙ (suc k))
-S^∙-even {k = k} n p  = ΣPathP ((funExt (-S^-even n p)) , lem k n p)
  where
  lem : (k n : ℕ) (p : _) → PathP (λ i → -S^-even n p (ptSn (suc k)) i ≡ ptSn (suc k))
                                   (-S^pt n) (λ _ → ptSn (suc k))
  lem k zero p = refl
  lem zero (suc (suc n)) p =
    (sym (rUnit _) ∙ cong (congS invSphere) (sym (rUnit _)))
    ◁ flipSquare (sym (rUnit _)
    ◁ λ i j → invLooper (invLooper (lem zero n p j i)))
  lem (suc k) (suc (suc n)) p =
    (cong₂ _∙_ (cong-∙ invSphere (cong invSphere (-S^pt n)) invSpherePt) refl
    ∙ sym (assoc _ _ _)
    ∙ cong₂ _∙_ refl (rCancel _)
    ∙ sym (rUnit _))
    ◁ flipSquare (sym (rUnit _) ◁ λ i j → invSphere (invSphere (lem (suc k) n p j i)))

-S^∙-odd : {k : ℕ} (n : ℕ) → isOddT n → -S^∙ {k = k} n ≡ (invSphere , invSpherePt)
-S^∙-odd {k = k} (suc n) o =
  cong ((invSphere , invSpherePt) ∘∙_) (-S^∙-even {k = k} n o) ∙ ∘∙-idˡ _

-S^-odd : {k : ℕ} (n : ℕ) → isOddT n → (x : S₊ (suc k)) → -S^ n x ≡ invSphere x
-S^-odd (suc zero) p x = refl
-S^-odd (suc (suc (suc n))) p x =
  cong (invSphere ∘ invSphere) (-S^-odd (suc n) p x)
  ∙ invSphere² _ (invSphere x)

-- -π'Invol :  ∀ {ℓ} {X : Pointed ℓ} {k : ℕ} (f : π' (suc k) X)
--   → -π' k (-π' k f)  ≡ f
-- -π'Invol f = GroupTheory.invInv (π'Gr _ _) f

[_∣_]π*-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
       → [ f ∣ g ]π* ≡ fun (π*SwapIso (suc m) (suc n) X) [ g ∣ f ]π*
[_∣_]π*-comm {n = n} {m = m} = elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f g → cong ∣_∣₂
    (WhiteheadProdComm'
        (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
        (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g
    ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f ∘∙_)
       (ΣPathP (refl , sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit _)))))

open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.S1.Base hiding (_·_)

cong-invsphere-σS : {k : ℕ} (x : S₊ (suc k))
  → Square (cong invSphere (σS x)) (σS (invSphere x))
            invSpherePt invSpherePt
cong-invsphere-σS {k = k} x =
  (cong-∙ invSusp (merid x) (sym (merid (ptSn (suc k))))
  ∙ refl)
  ◁ ((λ i → (λ j → merid (ptSn (suc k)) (~ i ∨ j))
          ∙∙ sym (merid x)
          ∙∙ (λ j → merid (ptSn (suc k)) (~ i ∧ j)))
  ▷ (sym (compPath≡compPath'
           (merid (ptSn (suc k))) (sym (merid x)))
  ∙ sym (symDistr (merid x) (sym (merid (ptSn (suc k)))))
  ∙ sym (σS-S^ 1 x)))

cong-S^σ : (n k : ℕ) (a : S₊ (suc n))
  → Square (σSn (suc n) (-S^ k a))
            (cong (-S^ k) (σS a))
            (sym (-S^pt k)) (sym (-S^pt k))
cong-S^σ n zero a = refl
cong-S^σ n (suc k) a i j =
  hcomp (λ r → λ{(i = i0) → cong-invsphere-σS (-S^ k a) r j
                ; (i = i1) → -S^ (suc k) (σS a j)
                ; (j = i0) → compPath-filler (cong invSphere (-S^pt k))
                                              invSpherePt r (~ i)
                ; (j = i1) → compPath-filler (cong invSphere (-S^pt k))
                                              invSpherePt r (~ i)})
        (invSphere (cong-S^σ n k a i j))

join-commFun-sphere→Join : (n m : ℕ) (x : _)
  → PathP (λ i → S₊ (suc (+-comm n m i)))
          (join→Sphere n m (join-commFun x))
          (-S^ (suc (m · n)) (join→Sphere m n x))
join-commFun-sphere→Join n m (inl x) =
    (λ i → ptSn (suc (+-comm n m i)))
  ▷ sym (-S^pt (suc (m · n)))
join-commFun-sphere→Join n m (inr x) =
  (λ i → ptSn (suc (+-comm n m i)))
  ▷ sym (-S^pt (suc (m · n)))
join-commFun-sphere→Join zero zero (push a b i) j = lem j i
  where
  main : (a b : Bool) → sym (σS (b ⌣S a)) ≡ cong (-S^ 1) (σS (a ⌣S b))
  main false false = refl
  main false true = refl
  main true false = refl
  main true true = refl

  lem : Square (sym (σS (b ⌣S a))) (cong (-S^ 1) (σS (a ⌣S b)))
               (refl ∙ (refl ∙ refl)) (refl ∙ (refl ∙ refl))
  lem = flipSquare (sym (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl))
    ◁ flipSquare (main a b)
    ▷ (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl)))

join-commFun-sphere→Join zero (suc m) (push a b i) j =
  comp (λ k → S₊ (suc (+-comm zero (suc m) (j ∧ k))))
       (λ k →
      λ{(i = i0) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
                   ▷ sym (-S^pt (suc (·-comm zero m k)))) j
      ; (i = i1) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
                   ▷ sym (-S^pt (suc (·-comm zero m k)))) j
      ; (j = i0) → σSn (suc m) (b ⌣S a) (~ i)
      ; (j = i1) → -S^ (suc (·-comm zero m k))
                      (σS (toPathP {A = λ i → S₊ (+-comm zero (suc m) i)}
                                   (sym (comm⌣S a b)) k) i)})
   (hcomp (λ k →
      λ{(i = i0) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
      ; (i = i1) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
      ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
      ; (j = i1) → cong-S^σ m (suc zero) (b ⌣S a) k i})
       (σ (S₊∙ (suc m)) (-S^ 1 (b ⌣S a)) i))
  where
  n = zero
  lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
  lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
      ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
      ∙ -S^·2 (m · n) (b ⌣S a)
join-commFun-sphere→Join (suc n') m (push a b i) j =
  comp (λ k → S₊ (suc (+-comm n m (j ∧ k))))
       (λ k →
      λ{(i = i0) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
                  ▷ sym (-S^pt (suc (m · n)))) j
      ; (i = i1) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
                  ▷ sym (-S^pt (suc (m · n)))) j
      ; (j = i0) → σSn (n + m) (b ⌣S a) (~ i)
      ; (j = i1) → -S^ (suc (m · n))
                        (σS (toPathP {A = λ i → S₊ (+-comm n m i)}
                                 (sym (comm⌣S a b)) k) i)})
   (hcomp (λ k →
      λ{(i = i0) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
      ; (i = i1) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
      ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
      ; (j = i1) → cong-S^σ (n' + m) (suc (m · n))
                             (-S^ (n · m) (b ⌣S a)) k i})
      (σ (S₊∙ (suc (n' + m))) (invSphere (lem (~ j))) i))
  where
  n = suc n'
  lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
  lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
      ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
      ∙ -S^·2 (m · n) (b ⌣S a)

-- todo: move elsewhere
open import Cubical.Data.Empty as ⊥

private
  -S^σS-lem : (n m : ℕ) (a : S₊ n) (b : S₊ m)
    → (1 ≤ n + m)
    → PathP
      (λ i₁ → -S^∙ {k = +-comm m n (~ i₁)} (suc (m · n)) .snd i₁
             ≡ -S^∙ (suc (m · n)) .snd i₁)
      ((cong (-S^ (suc (m · n)))
             (σS (subst S₊ (+-comm m n) (-S^ (m · n) (b ⌣S a))))))
      (σS (-S^ (suc (m · n)) (-S^ (m · n) (b ⌣S a))))
  -S^σS-lem zero zero a b ineq = ⊥.rec (snotz (+-comm 1 (ineq .fst) ∙ snd ineq))
  -S^σS-lem zero (suc m) a b ineq i j =
    cong-S^σ _ (suc (m · zero))
     (transp (λ j → S₊ (+-comm (suc m) zero (j ∧ ~ i)))
             i (-S^ (suc m · zero) (b ⌣S a))) (~ i) j
  -S^σS-lem (suc n) zero a b ineq i j =
    cong-S^σ _ (suc zero)
     (transp (λ j → S₊ (+-comm zero (suc n) (j ∧ ~ i)))
             i (b ⌣S a)) (~ i) j
  -S^σS-lem (suc n) (suc m) a b ineq i j =
    cong-S^σ _ (suc (suc m · suc n))
                   (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
                           i (-S^ (suc m · suc n) (b ⌣S a))) (~ i) j

open import Cubical.HITs.Truncation as TR
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation as PT


join→Sphere∘join-commFunId : (n m : ℕ) (x : _)
  → PathP (λ i → S₊ (suc (+-comm m n (~ i))))
           (-S^ (suc (m · n)) (join→Sphere n m x))
           (join→Sphere m n (join-commFun x))
join→Sphere∘join-commFunId n m (inl x) i = -S^∙ (suc (m · n)) .snd i
join→Sphere∘join-commFunId n m (inr x) i = -S^∙ (suc (m · n)) .snd i
join→Sphere∘join-commFunId zero zero (push a b i) j =
  (sym (rUnit refl) ◁  flipSquare (lem a b) ▷ rUnit refl) i j
  where
  lem : (a b : Bool) → cong invSphere (σS (a ⌣S b)) ≡ sym (σS (b ⌣S a))
  lem false false = refl
  lem false true = refl
  lem true false = refl
  lem true true = refl
join→Sphere∘join-commFunId (suc n') zero (push a b i) j = lem j i
  where
  n = suc n'
  m = zero
  lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
                (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
                (sym (σS (b ⌣S a)))
                (λ i → -S^∙ (suc (m · n)) .snd i)
                λ i → -S^∙ (suc (m · n)) .snd i
  lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
             (comm⌣S a b)
      ◁ -S^σS-lem n zero a b (n' + zero , +-comm (n' + zero) 1)
      ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
               ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
                               ∙ -S^·2 (m · n) (b ⌣S a)))
           ∙ σ-invSphere _ (b ⌣S a))
join→Sphere∘join-commFunId n (suc m') (push a b i) j = lem j i
  where
  m = suc m'
  lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
                (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
                (sym (σS (b ⌣S a)))
                (λ i → -S^∙ (suc (m · n)) .snd i)
                λ i → -S^∙ (suc (m · n)) .snd i
  lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
             (comm⌣S a b)
      ◁ -S^σS-lem n (suc m') a b (n + m' , +-comm (n + m') 1 ∙ sym (+-suc n m'))
      ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
               ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
                               ∙ -S^·2 (m · n) (b ⌣S a)))
           ∙ σ-invSphere _ (b ⌣S a))


open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Properties
-- JacobiΣR
open import Cubical.HITs.Join.CoHSpace
open import Cubical.Homotopy.HSpace
open import Cubical.HITs.SmashProduct.SymmetricMonoidal

·Susp≡ : ∀ {ℓ ℓ'} (A A' : Pointed ℓ) {X : Pointed ℓ'} (e : A ≃∙ A')
  → (f g : Susp∙ (typ A) →∙ X)
  → ·Susp A f g
   ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
               (g ∘∙ suspFun∙ (invEq (fst e)))
    ∘∙ suspFun∙ (fst (fst e)))
·Susp≡ A A' {X} = Equiv∙J (λ A e → (f g : Susp∙ (typ A) →∙ X) →
      ·Susp A f g
   ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
               (g ∘∙ suspFun∙ (invEq (fst e)))
     ∘∙ suspFun∙ (fst (fst e))))
 λ f g → sym (cong₂ _∘∙_ (cong₂ (·Susp A')
   (cong (f ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ f)
   (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g))
   (ΣPathP (suspFunIdFun , refl))
   ∙ ∘∙-idˡ (·Susp A' f g))


[_∣_]π'-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
    → [ f ∣ g ]π'
      ≡ subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
              (-π^ (m ·₋₁ n) [ g ∣ f ]π')
[_∣_]π'-comm {X = X} {n} {m} =
  PT.rec (isPropΠ2 (λ _ _ → squash₂ _ _)) (λ main →
  ST.elim2 (λ _ _ → isSetPathImplicit)
  λ f g → cong ∣_∣₂
    (cong (λ f → _∘∙_ {A = S₊∙ (suc (suc (n + suc m)))}
                      f (sphere→Join (suc n) (suc m)
                       , IsoSphereJoin⁻Pres∙ (suc n) (suc m)))
               (WhiteheadProdComm' (S₊∙ (suc n)) (S₊∙ n)
                 (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
                 (S₊∙ (suc m)) (S₊∙ m)
                 (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g)
               ∙ refl)
            ∙ cong ∣_∣₂ (∘∙-assoc (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f)
                                   join-commFun∙
                                   (sphere→Join (suc n) (suc m)
                                   , (λ _ → inl (ptSn (suc n)))))
            ∙ sym (fromPathP {A = λ i → π' (suc (+-comm (suc m) (suc n) i)) X}
                  ((-π^≡iter-Π (suc (suc m · suc n)) [ ∣ g ∣₂ ∣ ∣ f ∣₂ ]π'
                  ∙ cong ∣_∣₂ (iter-Π≡∘-S^ (suc (suc m · suc n)) [ g ∣ f ])
                  ∙ cong ∣_∣₂ (∘∙-assoc _ _ _))
                  ◁ λ i → ∣ [ g ∣ f ]-pre ∘∙ main i ∣₂))) main

  where
  main' : (x : _)
    → PathP (λ i → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
             (-S^ (suc (suc m · suc n)) (join→Sphere (suc n) (suc m) x))
             (join→Sphere (suc m) (suc n) (join-commFun x))
  main' (inl x) i = -S^∙ (suc (suc m · suc n)) .snd i
  main' (inr x) i = -S^∙ (suc (suc m · suc n)) .snd i
  main' (push a b i) j = lem j i
    where
    lem : SquareP (λ i j → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
                  (cong (-S^ (suc (suc m · suc n))) (σS (a ⌣S b)))
                  (sym (σS (b ⌣S a)))
                  (λ i → -S^∙ (suc (suc m · suc n)) .snd i)
                  λ i → -S^∙ (suc (suc m · suc n)) .snd i
    lem = cong (congS (-S^ (suc (suc m · suc n))) ∘ σS)
               (comm⌣S a b)
        ◁ (λ i j → cong-S^σ _ (suc (suc m · suc n))
                     (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
                             i (-S^ (suc (n + m · suc n)) (b ⌣S a))) (~ i) j)
        ▷ (cong σS ((λ i → -S^ (suc (suc m · suc n)) (-S^ ((suc m · suc n)) (b ⌣S a)))
                 ∙ cong invSphere (-S^-comp (suc m · suc n) (suc m · suc n) (b ⌣S a)
                                 ∙ -S^·2 (suc m · suc n) (b ⌣S a)))
             ∙ σ-invSphere _ (b ⌣S a))


  main : ∥ PathP (λ i → S₊∙ (suc (+-comm (suc m) (suc n) i))
                      →∙ join∙ (S₊∙ (suc m)) (S₊∙ (suc n)))
                 ((sphere→Join (suc m) (suc n) , refl)
                 ∘∙ -S^∙ (suc (suc m · suc n)))
                 (join-commFun∙ ∘∙ (sphere→Join (suc n) (suc m) , refl)) ∥₁
  main = TR.rec (isProp→isOfHLevelSuc (m + suc n) squash₁)
    (λ Q → ∣ ΣPathP (fstEq , Q) ∣₁)
    (isConnectedPathP _
      (isConnectedPath _
        (subst (isConnected (suc (suc (suc (m + suc n)))))
          (isoToPath (invIso (joinSphereIso' (suc m) (suc n))))
          (sphereConnected (suc (suc m + suc n))) ) _ _) _ _ .fst)
    where
    fstEq : PathP _ _ _
    fstEq = toPathP (funExt (λ s
      → ((transportRefl _
        ∙ cong (sphere→Join (suc m) (suc n))
           (sym (substCommSlice (λ n → S₊ (suc n)) (λ n → S₊ (suc n))
                                (λ _ → -S^ (suc (suc m · suc n)))
                                (sym (+-comm (suc m) (suc n)))
                                (join→Sphere (suc n) (suc m)
                                  (sphere→Join (suc n) (suc m) s))
               ∙ cong (-S^ (suc (suc m · suc n)))
                      (cong (subst (S₊ ∘ suc) (sym (+-comm (suc m) (suc n))))
                            (Iso.rightInv (IsoSphereJoin (suc n) (suc m)) s)))))
        ∙ cong (sphere→Join (suc m) (suc n))
               (fromPathP (main' (sphere→Join (suc n) (suc m) s))))
        ∙ Iso.leftInv (IsoSphereJoin (suc m) (suc n))
                       (join-commFun (sphere→Join (suc n) (suc m) s))))

open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

joinPinchComp : ∀ {ℓ ℓ' ℓ'' ℓA ℓB} {X : Pointed ℓ}
  {A : Type ℓA} {B : Type ℓB}
  {A' : Type ℓ'} {B' : Type ℓ''}
  (g : A → A') (h : B → B') 
  → (f : A' → B' → Ω X .fst) (x : join A B)
  → joinPinch X f (join→ g h x)
   ≡ joinPinch X (λ a b → f (g a) (h b)) x
joinPinchComp {X = X} g h f (inl x) = refl
joinPinchComp {X = X} g h f (inr x) = refl
joinPinchComp {X = X} g h f (push a b i) = refl

open import Cubical.Foundations.Pointed.Homogeneous

Ω→σ : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
  (f : Susp∙ (typ A) →∙ B)
  (g : C →∙ A)
  → (Ω→ f  ∘∙ (((σ A) , (rCancel _)) ∘∙ g))
   ≡ (Ω→ (f ∘∙ suspFun∙ (fst g)) ∘∙ (σ C , rCancel _))
Ω→σ {A = A} {B} {C} f g =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ x →
        cong (Ω→ f .fst)
          (sym (cong-∙ (suspFun (fst g)) (merid x) (sym (merid (pt C)))
                      ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (snd g))))))
  ∙ cong₂ _∘∙_ (cong Ω→ (ΣPathP (refl , lUnit (snd f)))) refl

private
  assocPath : (n m l : ℕ) → _ ≡ _
  assocPath n m l = (+-assoc (suc m) (suc n) (suc l)
                          ∙ cong (_+ suc l) (+-comm (suc m) (suc n))
                          ∙ +-assoc (suc n) (suc m) (suc l) ⁻¹)

SphereSmashIso∙ : (n m : ℕ) → Iso.fun (SphereSmashIso n m) (inl tt) ≡ ptSn (n + m)
SphereSmashIso∙ zero m = refl
SphereSmashIso∙ (suc n) m = refl

suspFun∙Cancel : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : Iso A B)
  → suspFun∙ (fun f) ∘∙ suspFun∙ (inv f)  ≡ id∙ (Susp∙ B)
suspFun∙Cancel f = ΣPathP ((funExt (rightInv (congSuspIso f)))
  , sym (rUnit refl))

SphereSmashIso⁻∙ : (n m : ℕ) → Iso.inv (SphereSmashIso n m) (ptSn (n + m)) ≡ inl tt
SphereSmashIso⁻∙ n m =
    sym (cong (Iso.inv (SphereSmashIso n m)) (SphereSmashIso∙ n m))
  ∙ Iso.leftInv (SphereSmashIso n m) (inl tt)

wh∘∙eq : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → {B' : Pointed ℓ'} → (e : B' ≃∙ B)
  → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
   ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e))
wh∘∙eq {A = A} {B} {C} {B'} =
  Equiv∙J (λ B' e → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
   ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e)))
   λ f g → cong (·whΣ A B f)
             (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g)
          ∙ (sym (∘∙-idˡ (·whΣ A B f g)))
          ∙ cong₂ _∘∙_ refl
              (sym (ΣPathP (suspFunIdFun , refl))
              ∙ cong suspFun∙ (sym
                 (cong fst ⋀→∙-idfun)))

wh∘∙eqL : ∀ {ℓ ℓ' ℓ''} {A A' : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (e : A' ≃∙ A)
  (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → ·whΣ A' B (f ∘∙ suspFun∙ (fst (fst e))) g
  ≡ (·whΣ A B f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ B))
wh∘∙eqL {A = A} {B} {C} {B'} =
  Equiv∙J (λ B e → (f : Susp∙ (typ A) →∙ B')
      (g : Susp∙ (typ C) →∙ B') →
      ·whΣ B C (f ∘∙ suspFun∙ (fst (fst e))) g ≡
      (·whΣ A C f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ C)))
    λ f g → cong₂ (·whΣ A C) (cong (f ∘∙_) suspFun∙idfun ∙ ∘∙-idˡ f) refl
           ∙ sym (∘∙-idˡ _)
           ∙ cong₂ _∘∙_ refl (sym
              (cong suspFun∙ (cong fst ⋀→∙-idfun)
              ∙ suspFun∙idfun))


open import Cubical.Foundations.Equiv.HalfAdjoint

retEqIsoToEquiv∙ : ∀ {ℓ} {A B : Pointed ℓ}
  (e : A ≃∙ B) (e∙ : invEq (fst e) (pt B) ≡ pt A)
  (eq : sym (secEq (fst e) (pt B))
      ∙ cong (fst (fst e)) e∙
      ≡ sym (snd e))
    → retEq (fst e) (pt A)
     ≡ cong (invEq (fst e)) (snd e)
     ∙ e∙
retEqIsoToEquiv∙ {A = A} {B} =
  Equiv∙J (λ A e → (e∙ : invEq (fst e) (pt B) ≡ pt A)
                    (eq : sym (secEq (fst e) (pt B))
                        ∙ cong (fst (fst e)) e∙
                        ≡ sym (snd e))
    → retEq (fst e) (pt A) ≡ cong (invEq (fst e)) (snd e) ∙ e∙)
    λ e∙ p → sym p

retEqIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (is : Iso A B) (x : _)
    → retEq (isoToEquiv is) x
     ≡ ((sym (leftInv is (inv is (fun is x)))
     ∙ cong (inv is) ((rightInv is (fun is x)))))
     ∙ leftInv is x
retEqIsoToEquiv is x i j =
  hcomp (λ k → λ {(i = i1) → compPath-filler (sym (leftInv is (inv is (fun is x)))
                              ∙ cong (inv is) ((rightInv is (fun is x)))) (leftInv is x) k j
                  ; (j = i0) → (cong (inv is) (sym (rightInv is (fun is x)))
                              ∙ leftInv is (inv is (fun is x))) (i ∨ k)
                  ; (j = i1) → lUnit (leftInv is x) (~ i) k
                  })
    (lemma j i)
  where
  p = sym (symDistr (sym (leftInv is (inv is (fun is x))))
                        (cong (inv is) (rightInv is (fun is x))))
  lemma : Square (cong (inv is) (sym (rightInv is (fun is x)))
                ∙ leftInv is (inv is (fun is x)))
          refl refl
          (sym (leftInv is (inv is (fun is x)))
         ∙ cong (inv is) ((rightInv is (fun is x))))
  lemma = p ◁ λ i j → p i1 (~ i ∧ j)

IsoSucSphereSusp≃∙ : (n : ℕ) → (S₊∙ (suc n)) ≃∙ (Susp∙ (S₊ n))
IsoSucSphereSusp≃∙ n .fst = isoToEquiv (IsoSucSphereSusp n)
IsoSucSphereSusp≃∙ n .snd = IsoSucSphereSusp∙' n

IsoSucSphereSuspInv≃∙ : (n : ℕ) → (Susp∙ (S₊ n)) ≃∙ S₊∙ (suc n)
IsoSucSphereSuspInv≃∙ n .fst = isoToEquiv (invIso (IsoSucSphereSusp n))
IsoSucSphereSuspInv≃∙ n .snd = IsoSucSphereSusp∙ n

IsoSucSphereSusp≃∙CompL : (n : ℕ)
  → (≃∙map (IsoSucSphereSusp≃∙ n)
   ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) ≡ idfun∙ _
IsoSucSphereSusp≃∙CompL n i .fst x = rightInv (IsoSucSphereSusp n) x i
IsoSucSphereSusp≃∙CompL zero i .snd j = rUnit (λ _ → north) (~ i) j
IsoSucSphereSusp≃∙CompL (suc n) i .snd j = rUnit (λ _ → north) (~ i) j

IsoSucSphereSusp≃∙CompR : (n : ℕ)
  → (≃∙map (IsoSucSphereSuspInv≃∙ n))
   ∘∙ ≃∙map (IsoSucSphereSusp≃∙ n) ≡ idfun∙ _
IsoSucSphereSusp≃∙CompR n i .fst x = leftInv (IsoSucSphereSusp n) x i
IsoSucSphereSusp≃∙CompR zero i .snd j = rUnit (λ _ → base) (~ i) j
IsoSucSphereSusp≃∙CompR (suc n) i .snd j = rUnit (λ _ → north) (~ i) j

Ω→σS≡Ω→σ : ∀ {ℓ} {X : Pointed ℓ} (n : ℕ) (f : S₊∙ (suc n) →∙ X) (a : S₊ n)
  → Ω→ f .fst (σS a)
   ≡ Ω→ (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) .fst (σ (S₊∙ n) a)
Ω→σS≡Ω→σ zero f true =
  cong₃ _∙∙_∙∙_ (cong sym (lUnit (snd f)))
    (sym (cong (congS (fst f ∘ fst (fst (IsoSucSphereSuspInv≃∙ zero))))
               (rCancel (merid true))))
    (lUnit (snd f))
Ω→σS≡Ω→σ zero f false =
  cong₃ _∙∙_∙∙_ (cong sym (lUnit (snd f)))
    (cong (congS (fst f))
      (rUnit _
      ∙ sym (cong-∙ SuspBool→S¹ (merid false) (sym (merid true)))))
    (lUnit (snd f))
Ω→σS≡Ω→σ (suc n) f a = cong (λ f → Ω→ f .fst (σS a)) (sym (∘∙-idˡ f))

[]≡·whΣ' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
  (f : S₊∙ (suc n) →∙ X) (g : S₊∙ (suc m) →∙ X)
  →  [ f ∣ g ]
   ≡ (·whΣ (S₊∙ n) (S₊∙ m)
           (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
           (g ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))
    ∘∙ (suspFun∙ (inv (SphereSmashIso n m))
    ∘∙ (fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m))))
[]≡·whΣ' {X = X} {n} {m} f g =
  cong₂ _∘∙_ ((cong₂ [_∣_]-pre
        (sym (∘∙-idˡ _)
        ∙ cong₂ _∘∙_ refl (sym (IsoSucSphereSusp≃∙CompR n))
        ∙ sym (∘∙-assoc f _ _))
        (sym (∘∙-idˡ _)
        ∙ cong₂ _∘∙_ refl (sym (IsoSucSphereSusp≃∙CompR m))
        ∙ sym (∘∙-assoc g _ _)))) refl
  ∙ cong₂ _∘∙_
     (cong (joinPinch∙ (S₊∙ n) (S₊∙ m) X) (funExt (λ a → funExt λ b →
       cong₂ _∙_ (Ω→lemma m b g) (Ω→lemma n a f))))
     (ΣPathP (refl , sym (lem' n m) ∙ lUnit _))
  ∙ cong₂ _∘∙_ (·whΣ≡·wh (S₊∙ n) (S₊∙ m)
           (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
           (g ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)))
           (refl {x = ≃∙map (invEquiv∙ (joinSphereEquiv∙ n m))})
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl
          (cong (_∘∙ ≃∙map (invEquiv∙ (joinSphereEquiv∙ n m)))
                (lem n m)
          ∙ ∘∙-assoc _ _ _
          ∙ cong₂ _∘∙_ refl
            ((cong₂ _∘∙_ (sym (∘∙-idˡ _)) refl)
            ∙ rightInv (post∘∙equiv (joinSphereEquiv∙ n m)) (idfun∙ _))
          ∙ ∘∙-idˡ _)
  where
  Ω→lemma : (n : ℕ) (a : S₊ n) (f : S₊∙ (suc n) →∙ X)
    → Ω→ ((f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
                ∘∙ ≃∙map (IsoSucSphereSusp≃∙ n)) .fst (σS a)
     ≡ Ω→ (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) .fst (σ (S₊∙ n) a)
  Ω→lemma n a f =
      cong (λ f → Ω→ f .fst (σS a))
        ((∘∙-assoc f _ _
        ∙ cong₂ _∘∙_ refl (IsoSucSphereSusp≃∙CompR n))
       ∙ ∘∙-idˡ f)
    ∙ Ω→σS≡Ω→σ n f a

  lemL : (n m : ℕ) →
      suspFun (inv (SphereSmashIso n m))
      (fun (IsoSucSphereSusp (n + m)) (ptSn (suc (n + m))))
    ≡ north
  lemL zero zero = refl
  lemL zero (suc m) = refl
  lemL (suc n) m = refl

  lemR : (n m : ℕ) →
      suspFun (inv (SphereSmashIso n m))
      (fun (IsoSucSphereSusp (n + m)) (ptSn (suc (n + m))))
    ≡ south
  lemR zero zero = merid (inl tt)
  lemR zero (suc m) = merid (inl tt)
  lemR (suc n) m = merid (inl tt)

  lemma : (n m : ℕ) (a : S₊ n) (b : S₊ m)
    → Square {A = Susp (S₊∙ n ⋀ S₊∙ m)}
              (merid (inr (a , b)))
              (cong (suspFun (inv (SphereSmashIso n m)))
               (cong (fun (IsoSucSphereSusp (n + m)))
                (cong (fst (fst (joinSphereEquiv∙ n m))) (push a b))))
              (sym (lemL n m))
              (sym (lemR n m))
  lemma zero zero false false =
    compPath-filler (merid (inr (false , false))) (sym (merid (inl tt)))
      ▷ (cong₂ _∙_ refl (cong (sym ∘ merid) (push (inl false)))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero zero))) _ _))
  lemma zero zero false true =
    cong merid (sym (push (inl false))) ◁ λ i j → merid (inl tt) (~ i ∧ j)
  lemma zero zero true b =
    cong merid (sym (push (inr b))) ◁ λ i j → merid (inl tt) (~ i ∧ j)
  lemma zero (suc m) false b =
      compPath-filler (merid (inr (false , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_ refl (cong (sym ∘ merid) (push (inl false)))
    ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero (suc m)))) _ _))
  lemma zero (suc m) true b =
    cong merid (sym (push (inr b)))
    ◁ compPath-filler (merid (inl tt)) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_ (cong merid (push (inl false)))
                 (cong (sym ∘ merid) (push (inl false)))
    ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero (suc m)))) _ _))
  lemma (suc n) zero a b =
    compPath-filler (merid (inr (a , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_
       (cong merid (sym (leftInv (SphereSmashIso (suc n) zero)
                          (inr (a , b)))))
       (cong (sym ∘ merid) (sym (SphereSmashIso⁻∙ (suc n) zero)))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso (suc n) zero))) _ _))
  lemma (suc n) (suc m) a b =
    compPath-filler (merid (inr (a , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_
       (cong merid (sym (leftInv (SphereSmashIso (suc n) (suc m))
                          (inr (a , b)))))
       (cong (sym ∘ merid) (sym (SphereSmashIso⁻∙ (suc n) (suc m))))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso (suc n) (suc m)))) _ _))

  lem : (n m : ℕ)
    → Join→SuspSmash∙ (S₊∙ n) (S₊∙ m)
    ≡ (suspFun∙ (inv (SphereSmashIso n m))
    ∘∙ (fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m)))
    ∘∙ ≃∙map (joinSphereEquiv∙ n m)
  lem n m i .fst (inl x) = lemL n m (~ i)
  lem n m i .fst (inr x) = lemR n m (~ i)
  lem n m i .fst (push a b j) = lemma n m a b i j
  lem zero zero i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j
  lem zero (suc m) i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j
  lem (suc n) m i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j

  F : _ →∙ _
  F = fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m)

  p1 : (n m : ℕ) → leftInv (joinSphereIso' (suc n) m) (inl (ptSn (suc n)))
                    ≡ sym (push (ptSn (suc n)) (ptSn m))
  p1 n m =
    cong₂ _∙_ (cong (congS (inv (invIso SmashJoinIso))) (sym (rUnit refl))) refl
     ∙ sym (lUnit _)

  p2 : (n m : ℕ) → rightInv (joinSphereIso' (suc n) m) (ptSn (suc (suc n + m)))
                  ≡ sym (merid (ptSn (suc n + m)))
  p2 n m = cong₂ _∙_ (cong (sym ∘ merid) (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))))
       (sym (rUnit refl))
       ∙ sym (rUnit _)

  compPath-filler-diag : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → Path (Path A _ _) (λ i → compPath-filler p q (~ i) i) p
  compPath-filler-diag p q j i = compPath-filler p q (~ i ∧ ~ j) i

  p3 : (m : ℕ) → push true (ptSn (suc m))
                ∙ leftInv (joinSphereIso' zero (suc m)) (inl true)
                ≡ refl
  p3 m = cong₂ _∙_ refl
      (cong₂ _∙_ (cong (congS (fun SmashJoinIso))
                       (sym (rUnit (λ _ → north)))) refl
      ∙ sym (lUnit _))
    ∙ rCancel (push true (ptSn (suc m)))

  lem' :  (n m : ℕ) → retEq (isoToEquiv (IsoSphereJoin n m)) (inl (ptSn n))
                       ≡ IsoSphereJoin⁻Pres∙ n m 
  lem' n m = retEqIsoToEquiv∙
    (isoToEquiv (IsoSphereJoin n m) , IsoSphereJoinPres∙ n m)
    (IsoSphereJoin⁻Pres∙ n m) (oh n m)
    ∙ sym (lUnit (IsoSphereJoin⁻Pres∙ n m))
    where
    dd = join→Sphere≡

    lemma3 : (n m : ℕ)
      → (λ i → join→Sphere≡ (suc n) m
                 (push (ptSn (suc n)) (ptSn m) (~ i)) (~ i))
       ≡ sym (merid (ptSn (suc (n + m))))
    lemma3 n m = flipSquare
      ((λ i j → join→Sphere≡ (suc n) m
                      (push (ptSn (suc n)) (ptSn m) (~ i ∨ j)) (~ i))
     ▷ (cong σS (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))) ∙ σS∙))

    oh : (n m : ℕ)
      → sym (secEq (isoToEquiv (IsoSphereJoin n m)) (ptSn (suc (n + m))))
       ∙ cong (join→Sphere n m) (IsoSphereJoin⁻Pres∙ n m)
       ≡ sym (IsoSphereJoinPres∙ n m)
    oh zero zero =
      cong₂ _∙_ (cong sym (sym (lUnit _)
               ∙ sym (lUnit (refl ∙ refl)) ∙ sym (rUnit refl))) refl
     ∙ sym (rUnit refl)
    oh zero (suc n) =
        cong₂ _∙_ (cong₃ _∙∙_∙∙_
          (cong sym (cong₂ _∙_ refl (sym (rUnit refl)) ∙ sym (rUnit _)))
          (λ j i → compPath-filler (merid (ptSn (suc n)))
                     (sym (merid (ptSn (suc n)))) (i ∧ ~ j) (~ i))
          refl) refl
      ∙ cong sym (sym (rUnit _) ∙ rCancel (merid (ptSn (suc n))))
    oh (suc n) m = cong₂ _∙_ (cong₃ _∙∙_∙∙_
      (cong sym (cong₂ _∙_ refl (sym (rUnit refl)) ∙ sym (rUnit _))
              ∙ cong merid (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))))
                             (lemma3 n m) refl
                           ∙ cong sym (rCancel (merid (ptSn (suc (n + m))))))
                           refl
                           ∙ sym (rUnit refl)

[]≡·whΣ : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  →  [ f ∣ g ]
   ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g
   ∘∙ suspFun∙ (inv (SphereSmashIso (suc n) (suc m))))
[]≡·whΣ {X = X} {n} {m} f g = []≡·whΣ'  {X = X} f g
  ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)))
               (∘∙-idˡ f) (∘∙-idˡ g))
               (∘∙-idˡ (suspFun∙ (inv (SphereSmashIso (suc n) (suc m)))))

tripleSmasherL≃∙ : {n m l : ℕ}
  → S₊∙ (suc n + (suc m + suc l))
  ≃∙ S₊∙ (suc n) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))
tripleSmasherL≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m + suc l)))
                        , SphereSmashIso⁻∙ (suc n) (suc m + suc l))
             (⋀≃ (idEquiv∙ (S₊∙ (suc n)))
             ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l))))
                                , (SphereSmashIso⁻∙ (suc m) (suc l)))
            , refl)

tripleSmasherR≃∙ : {n m l : ℕ}
  → S₊∙ ((suc n + suc m) + suc l)
  ≃∙ ((S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) ⋀∙ S₊∙ (suc l))
tripleSmasherR≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n + suc m) (suc l)))
                        , SphereSmashIso⁻∙ (suc n + suc m) (suc l))
             (⋀≃ ((isoToEquiv (invIso (SphereSmashIso (suc n) (suc m))))
                                    , (SphereSmashIso⁻∙ (suc n) (suc m)))
                 (idEquiv∙ (S₊∙ (suc l)))
            , refl)

tripleSmasherL≃∙Id : (n m l : ℕ) (x : _)
  → PathP (λ i → Susp (S₊ (assocPath n m l (~ i))))
           (suspFun (-S^ (suc n · suc m)
                   ∘ invEq (fst (tripleSmasherL≃∙ {n = n} {m} {l}))) x)
           (suspFun (invEq (fst (tripleSmasherL≃∙ {n = m} {n} {l}))
                   ∘ inv SmashAssocIso
                   ∘ (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                   ∘ fun SmashAssocIso) x)
tripleSmasherL≃∙Id n m l north i = north
tripleSmasherL≃∙Id n m l south i = south
tripleSmasherL≃∙Id n m l (merid a i) j = lem a j i
  where
  lemma : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
    → PathP (λ i → S₊ (assocPath n m l (~ i)))
             (-S^ (suc n · suc m) (invEq (fst tripleSmasherL≃∙)
               (inr (x , inr (y , z)))))
              (invEq (fst tripleSmasherL≃∙)
               (inv SmashAssocIso
                ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                 (fun SmashAssocIso (inr (x , inr (y , z)))))))
  lemma x y z = transport (λ j →
    PathP (λ i → S₊ (isSetℕ _ _ p (sym (assocPath n m l)) j i))
          (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
          (y ⌣S (x ⌣S z)))
        help
    where
    p = (cong suc (+-assoc n (suc m) (suc l))
       ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
       ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

    help : PathP (λ i → S₊ (p i))
                 (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
                 (y ⌣S (x ⌣S z))
    help =
      compPathP' {B = S₊}
      (compPathP' {B = S₊}
        (λ i → -S^ (suc n · suc m) (assoc⌣S x y z i))
        (λ i → -S^ (suc n · suc m)
           (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
                    (sym (comm⌣S x y)) (~ i) ⌣S z))
      ▷ (cong (-S^ (suc n · suc m))
                (⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
               ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))
      ∙ -S^² (suc n · suc m) ((y ⌣S x) ⌣S z)))
      (symP (assoc⌣S y x z))

  lem : (a : _)
    → SquareP (λ i j → Susp (S₊ (assocPath n m l (~ i))))
               (merid ((-S^ (suc n · suc m) ∘ invEq (fst tripleSmasherL≃∙)) a))
               (merid (invEq (fst tripleSmasherL≃∙)
                        (inv SmashAssocIso
                         ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                          (fun SmashAssocIso a)))))
               (λ _ → north)
               (λ _ → south)
  lem = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
    λ x → ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
      λ y z i → merid (lemma x y z i)

·whΣ-assocer : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  (h : S₊∙ (2 + l) →∙ X)
  → [ f ∣ [ g ∣ h ] ]
   ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) f
       (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h)
   ∘∙ suspFun∙ (fst (fst tripleSmasherL≃∙)))
·whΣ-assocer {X = X} {n} {m} {l} f g h =
    cong₂ [_∣_] refl ([]≡·whΣ {X = X} g h)
  ∙ []≡·whΣ f _
  ∙ cong₂ _∘∙_
      (wh∘∙eq ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l))))
                                 , (SphereSmashIso⁻∙ (suc m) (suc l))) f
             (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h))
      refl
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl (sym (suspFun∙Comp _ _))

·whΣ-assocerR : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  (h : S₊∙ (2 + l) →∙ X)
  → [ [ f ∣ g ] ∣ h ]
   ≡ (·whΣ (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l)) 
       (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h
   ∘∙ suspFun∙ ((fst (fst tripleSmasherR≃∙))))
·whΣ-assocerR {X = X} {n} {m} {l} f g h =
  cong₂ [_∣_]  ([]≡·whΣ {X = X} f g) refl
  ∙ []≡·whΣ _ _
  ∙ cong₂ _∘∙_ (wh∘∙eqL (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m)))
                                 , (SphereSmashIso⁻∙ (suc n) (suc m)))
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h) refl
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl
    (sym (suspFun∙Comp _ _))

subst∙ : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
  → {x y : X} (p : x ≡ y) → A x →∙ A y 
subst∙ A p .fst = subst (fst ∘ A) p
subst∙ A p .snd i = transp (λ j → fst (A (p (i ∨ j)))) i (pt (A (p i)))

subst∙refl : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
  → {x : X} → subst∙ A (refl {x = x}) ≡ idfun∙ (A x)
subst∙refl A {x} = ΣPathP ((funExt transportRefl)
  , (λ j i → transp (λ t → fst (A x)) (j ∨ i) (pt (A x))))

subst∙Id : ∀ {ℓ ℓA ℓB} {X : Type ℓ} (A : X → Pointed ℓA) {B : Pointed ℓB}
  → {x y : X} (p : x ≡ y) (f : A x →∙ B)
    → f ∘∙ subst∙ A (sym p) ≡ transport (λ i → A (p i) →∙ B) f 
subst∙Id A {B = B} {x = x} =
  J (λ y p → (f : A x →∙ B)
            → f ∘∙ subst∙ A (sym p)
            ≡ transport (λ i → A (p i) →∙ B) f)
    λ f → (cong₂ _∘∙_ refl (subst∙refl A) ∙ ∘∙-idˡ _)
         ∙ sym (transportRefl f)

private
  ∘∙preSubstLem : ∀ {ℓ} {X : Type ℓ} (n m : ℕ)
    (p : n ≡ m)
    (f : S₊ (suc m) → X)
    → suspFun∙ (f ∘ subst S₊ (cong suc p))
    ≡ (suspFun∙ f ∘∙ subst∙ (S₊∙ ∘ suc) (cong suc p))
  ∘∙preSubstLem n = J> λ f
    → (cong suspFun∙ (funExt (λ x → cong f (transportRefl x)))
    ∙ sym (∘∙-idˡ _))
    ∙ cong₂ _∘∙_ refl (sym (subst∙refl S₊∙))

suspFun∙substLem : ∀ {ℓ} {X : Type ℓ} {n m : ℕ}
  (p : suc n ≡ suc m)
  (f : S₊ (suc m)  → X)
  → suspFun∙ (f ∘ subst S₊ p)
  ≡ suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p
suspFun∙substLem p f =
  cong (λ p → suspFun∙ (f ∘ subst S₊ p)) (isSetℕ _ _ p (cong suc (cong predℕ p)))
  ∙ ∘∙preSubstLem _ _ _ f
  ∙ cong (λ p → suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p) (isSetℕ _ _ (cong suc (cong predℕ p)) p)



[∣]π'-distrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f g : π' (suc (suc n)) X) (h : π' (suc m) X)
       → [ ·π' (suc n) f g ∣ h ]π'
          ≡ ·π' _ [ f ∣ h ]π' [ g ∣ h ]π'
[∣]π'-distrL {X = X} {n} {m} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
       (lem n m (·Susp (S₊∙ (suc n)) f g) h
     ∙ (cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc n) m)))
              (WhiteheadProdΣBilinₗ
                (S₊∙ (suc n)) (S₊∙ n) (IsoSucSphereSusp≃∙ n) (S₊∙ m) f g (h *))
     ∙ cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc n) m)))
         (·Susp≡ (S₊∙ (suc n) ⋀∙ (S₊ m , ptSn m)) (S₊∙ (suc (n + m)))
            (isoToEquiv (SphereSmashIso (suc n) m) , refl)
            (·whΣ (S₊∙ (suc n)) (S₊ m , ptSn m) f (h *))
            (·whΣ (S₊∙ (suc n)) (S₊ m , ptSn m) g (h *)))
     ∙ ∘∙-assoc _ _ _
     ∙ cong₂ _∘∙_ refl
       (sym (suspFun∙Comp (fun (SphereSmashIso (suc n) m))
                     (inv (SphereSmashIso (suc n) m)))
     ∙ cong suspFun∙ (funExt (rightInv (SphereSmashIso (suc n) m)))
     ∙ suspFun∙idfun)
     ∙ ∘∙-idˡ _)
     ∙ cong₂ (·Susp (S₊∙ (suc (n + m))))
             (sym (lem n m f h))
             (sym (lem n m g h)))
  where
  _* : {m : ℕ} (h : S₊∙ (suc m) →∙ X) → _
  _* {m = m} h = h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)

  module _ (n m : ℕ) (f : S₊∙ (suc (suc n)) →∙ X) (h : S₊∙ (suc m) →∙ X) where
    lem : [ f ∣ h ]
        ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ m) f (h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))
          ∘∙ (suspFun∙ (inv (SphereSmashIso (suc n) m))))
    lem = []≡·whΣ' f h
        ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ (suc n)) (S₊∙ m)) (∘∙-idˡ f) refl)
                     (∘∙-idˡ (suspFun∙ (inv (SphereSmashIso (suc n) m))))

[∣]π'-distrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc n) X) (g h : π' (suc (suc m)) X)
       → [ f ∣ ·π' (suc m) g h ]π'
          ≡ ·π' _ [ f ∣ g ]π' [ f ∣ h ]π'
[∣]π'-distrR {X = X} {n} {m} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
      ([]≡·whΣ' f (·Susp (S₊∙ (suc m)) g h)
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m))) refl
                    (∘∙-idˡ (·Susp (S₊∙ (suc m)) g h))) refl
      ∙ cong₂ _∘∙_ (WhiteheadProdΣBilinᵣ (S₊∙ n) (S₊∙ (suc m)) (S₊∙ m) (IsoSucSphereSusp≃∙ m)
                    (f *) g h) refl
      ∙ main n m f g h
      ∙ cong₂ ∙Π (cong₂ _∘∙_
        (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m)) ) refl (sym (∘∙-idˡ g))) refl
        ∙ sym ([]≡·whΣ' f g))
        (cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m)) ) refl (sym (∘∙-idˡ h))) refl
        ∙ sym ([]≡·whΣ' f h)))
  where
  cor : (n m : ℕ) → _ →∙ _
  cor n m =
    (suspFun∙ (inv (SphereSmashIso n (suc m))) ∘∙
     (fun (IsoSucSphereSusp (n + suc m)) ,
      IsoSucSphereSusp∙' (n + suc m)))

  _* : {m : ℕ} (h : S₊∙ (suc m) →∙ X) → _
  _* {m = m} h = h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)

  main : (n m : ℕ) (f : S₊∙ (suc n) →∙ X) (g h : S₊∙ (suc (suc m)) →∙ X)
    → (·Susp (S₊∙ n ⋀∙ S₊∙ (suc m))
              (·whΣ (S₊∙ n) (S₊∙ (suc m)) (f *) g)
              (·whΣ (S₊∙ n) (S₊∙ (suc m)) (f *) h)
       ∘∙ cor n m)
    ≡ ∙Π (·whΣ (S₊∙ n) (S₊∙ (suc m))
               (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) g
       ∘∙ cor n m)
         (·whΣ (S₊∙ n) (S₊∙ (suc m))
               (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) h
       ∘∙ cor n m)
  main zero m f g h =
      cong₂ _∘∙_ (·Susp≡ (S₊∙ zero ⋀∙ S₊∙ (suc m))
                 (S₊∙ (suc m))
                 (isoToEquiv (SphereSmashIso zero (suc m)) , refl)
                 (·whΣ (S₊∙ zero) (S₊∙ (suc m)) (f *) g)
                 (·whΣ (S₊∙ zero) (S₊∙ (suc m)) (f *) h))
                 (∘∙-idˡ (suspFun∙ (λ y → inr (false , y))))
    ∙ ∘∙-assoc _ _ _
    ∙ cong₂ _∘∙_ refl
        (ΣPathP (funExt (secEq (isoToEquiv
                  (congSuspIso (SphereSmashIso zero (suc m)))))
                  , sym (rUnit refl)))
    ∙ ∘∙-idˡ _
    ∙ cong₂ (·Susp (S₊∙ (suc m)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
  main (suc n) m f g h =
    cong₂ _∘∙_ (·Susp≡ (S₊∙ (suc n) ⋀∙ S₊∙ (suc m))
               (S₊∙ (suc (n + suc m)))
               (isoToEquiv (SphereSmashIso (suc n) (suc m)) , refl)
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) (f *) g)
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) (f *) h)) refl
    ∙ ∘∙-assoc _ _ _
    ∙ cong₂ _∘∙_ refl (ΣPathP
      ((funExt (secEq (isoToEquiv (congSuspIso (SphereSmashIso (suc n) (suc m))))))
      , sym (rUnit _)
      ∙ cong (congS (suspFun (fun (SphereSmashIso (suc n) (suc m)))))
                    (sym (rUnit refl))))
    ∙ ∘∙-idˡ _
    ∙ cong₂ (·Susp (S₊∙ (suc (n + suc m))))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))


[∣]π'-idL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
   (g : π' (suc m) X) → [ 1π' (suc n) ∣ g ]π' ≡ 1π' (suc (n + m))
[∣]π'-idL {n = n} {m} =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ ([]≡·whΣ' 1Π f
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ m))
                          (ΣPathP (refl , sym (rUnit refl))) refl
      ∙ WhiteheadProdΣIdL (S₊∙ n) (S₊∙ m)
         (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))) refl
      ∙ ΣPathP (refl , (sym (rUnit refl))))

[∣]π'-idR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
   (f : π' (suc n) X) → [ f ∣ 1π' (suc m) ]π' ≡ 1π' (suc (n + m))
[∣]π'-idR {n = n} {m} =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ ([]≡·whΣ' f 1Π
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ m)) refl
                          (ΣPathP (refl , sym (rUnit refl)))
      ∙ WhiteheadProdΣIdR (S₊∙ n) (S₊∙ m)
         (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))) refl
      ∙ ΣPathP (refl , (sym (rUnit refl))))

[∣]π'-invDistrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc m) X)
       → [ -π' (suc n) f ∣ g ]π'
        ≡ -π' (suc (n + m)) [ f ∣ g ]π'
[∣]π'-invDistrL {n = n} {m} f g =
    sym (sym (π'-assoc (suc (n + m)) [ -π' (suc n) f ∣ g ]π'
                                     [ f ∣ g ]π' (-π' (suc (n + m))
                                     [ f ∣ g ]π'))
    ∙ cong₂ (·π' (suc (n + m))) refl (π'-rCancel (suc (n + m)) [ f ∣ g ]π')
    ∙ π'-rUnit _ ([ -π' (suc n) f ∣ g ]π'))
  ∙ cong (λ x → ·π' (suc (n + m)) x (-π' (suc (n + m)) [ f ∣ g ]π'))
         (sym ([∣]π'-distrL (-π' (suc n) f) f g))
  ∙ cong₂ (·π' (suc (n + m)))
          (cong [_∣ g ]π' (π'-lCancel (suc n) f) ∙ [∣]π'-idL g) refl
  ∙ π'-lUnit _ (-π' (suc (n + m)) [ f ∣ g ]π')

[∣]π'-invDistrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc n) X) (g : π' (suc (suc m)) X)
       → [ f ∣ -π' (suc m) g ]π'
        ≡ -π' (n + suc m) [ f ∣ g ]π'
[∣]π'-invDistrR {n = n} {m} f g =
    sym (sym (π'-assoc (n + suc m)
               [ f ∣ -π' (suc m) g ]π'
               [ f ∣ g ]π'
               (-π' (n + suc m) [ f ∣ g ]π'))
    ∙ cong₂ (·π' (n + suc m)) refl
            (π'-rCancel (n + suc m) [ f ∣ g ]π')
    ∙ π'-rUnit _ ([ f ∣ -π' (suc m) g ]π'))
  ∙ cong (λ x → ·π' (n + suc m) x (-π' (n + suc m) [ f ∣ g ]π'))
         (sym ([∣]π'-distrR f (-π' (suc m) g) g))
  ∙ cong₂ (·π' (n + suc m))
          (cong [ f ∣_]π' (π'-lCancel (suc m) g) ∙ [∣]π'-idR f) refl
  ∙ π'-lUnit _ (-π' (n + suc m) [ f ∣ g ]π')

[∣]π'-inv^DistrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ} (k : ℕ)
       (f : π' (suc (suc n)) X) (g : π' (suc m) X)
       → [ -π^ k f ∣ g ]π' ≡ -π^ k [ f ∣ g ]π'
[∣]π'-inv^DistrL {n = n} {m} zero f g = refl
[∣]π'-inv^DistrL {n = n} {m} (suc k) f g =
    [∣]π'-invDistrL (-π^ k f) g
  ∙ cong (-π' _) ([∣]π'-inv^DistrL k f g)

[∣]π'-inv^DistrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ} (k : ℕ)
       (f : π' (suc n) X) (g : π' (suc (suc m)) X)
       → [ f ∣ -π^ k g ]π' ≡ -π^ k [ f ∣ g ]π'
[∣]π'-inv^DistrR {n = n} {m} zero f g = refl
[∣]π'-inv^DistrR {n = n} {m} (suc k) f g =
    [∣]π'-invDistrR f (-π^ k g)
  ∙ cong (-π' _) ([∣]π'-inv^DistrR k f g)

[_∣_]π'Jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : π' (suc (suc n)) X)
  (g : π' (suc (suc m)) X)
  (h : π' (suc (suc l)) X)
  → [ f ∣ [ g ∣ h ]π' ]π'
   ≡ ·π' _ (subst (λ k → π' k X)
                  (cong (2 +_) (sym (+-assoc n (suc m) (suc l))))
                  ([ [ f ∣ g ]π' ∣ h ]π'))
           (subst (λ k → π' k X)
                  (cong suc (assocPath n m l))
                  (-π^ (suc n · suc m) [ g ∣ [ f ∣ h ]π' ]π'))
[_∣_]π'Jacobi {X = X} {n} {m} {l} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
       (·whΣ-assocer f g h
      ∙ cong₂ _∘∙_
        (JacobiΣR' (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
          (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
          (S₊∙ (suc l)) (S₊∙ l)
          (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
          f g h) refl
      ∙ cong₂ _∘∙_ (·Susp≡ _ _ (invEquiv∙ tripleSmasherL≃∙) _ _) refl
      ∙ ∘∙-assoc _ _ _
      ∙ cong₂ _∘∙_ refl
        (sym (suspFun∙Comp _ _)
        ∙ cong suspFun∙ (funExt (retEq (fst tripleSmasherL≃∙))) ∙ suspFun∙idfun)
      ∙ ∘∙-idˡ _
      ∙ cong₂ (·Susp (S₊∙ (suc (n + suc (m + suc l)))))
              (sym (sym (subst∙Id (S₊∙ ∘ (2 +_))
                          (sym (+-assoc n (suc m) (suc l)))
                          [ [ f ∣ g ] ∣ h ])
                 ∙ cong₂ _∘∙_ (·whΣ-assocerR f g h) (λ _ → s1)
                 ∙ ∘∙-assoc _ _ _
                 ∙ cong₂ _∘∙_ refl (ΣPathP ((funExt λ { north → refl
                                                      ; south → refl
                                                      ; (merid a i) j → hoo a j i})
                                                      , sym (rUnit refl)) ∙ suspFun∙Comp _ _)
                 ∙ sym (∘∙-assoc _ _ _)))
              (sym (cong (transport (λ i → S₊∙ (suc (assocPath n m l i)) →∙ X))
                         (iter-Π≡∘-S^ deg _)
                  ∙ (sym (subst∙Id (S₊∙ ∘ suc)
                          (assocPath n m l) _)
                  ∙ cong₂ _∘∙_ (cong₂ _∘∙_ (·whΣ-assocer g f h)
                                          (-S^∙suspFun deg)
                             ∙ ∘∙-assoc _ _ _
                             ∙ cong₂ _∘∙_ refl
                               (sym (suspFun∙Comp (fst (fst tripleSmasherL≃∙))
                                                  (-S^ deg)))) refl)
                  ∙ ∘∙-assoc _ _ _
                  ∙ cong₂ _∘∙_ refl
                    ((cong₂ _∘∙_ refl
                      refl
                    ∙ sym (suspFun∙substLem (sym (assocPath n m l))
                            (fst (fst tripleSmasherL≃∙) ∘ -S^ deg))
                    ∙ final-lemma)
                    ∙ suspFun∙Comp _ _)
                  ∙ sym (∘∙-assoc _ _ _))))
       ∙ refl
       ∙ cong₂ (·π' (suc (n + suc (m + suc l)))) refl
               (cong (subst (λ k → π' k X) (cong suc (assocPath n m l)))
                     (sym (-π^≡iter-Π deg _)))
  where
  deg = suc n · suc m

  meridLem1 : (a : S₊ (suc (n + suc (m + suc l))))
    → merid (fst (fst tripleSmasherL≃∙)
              (-S^ deg (subst S₊ (sym (assocPath n m l)) a)))
     ≡ merid (inv SmashAssocIso
              ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
               (fun SmashAssocIso (fst (fst tripleSmasherL≃∙) a))))
  meridLem1 a =
      cong merid (cong (fst (fst tripleSmasherL≃∙)
                      ∘ -S^ deg
                      ∘ subst S₊ (sym (assocPath n m l)))
                 (sym (retEq (fst tripleSmasherL≃∙) a)))
    ∙ meridLem2 (fst (fst tripleSmasherL≃∙) a)
    where
    meridLem2 : (a : _)
      → merid (fst (fst tripleSmasherL≃∙)
                (-S^ deg
                 (subst S₊ (sym (assocPath n m l))
                  (invEq (fst tripleSmasherL≃∙) a))))
       ≡ merid (inv SmashAssocIso
                ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                 (fun SmashAssocIso a))) 
    meridLem2 =
      ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
       λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
         λ y z → cong merid
           (refl
           ∙ cong (fst (fst tripleSmasherL≃∙) ∘ -S^ deg)
                 (meridLem3 x y z)
          ∙ cong (fst (fst tripleSmasherL≃∙))
                 (-S^² deg _)
          ∙ secEq (fst tripleSmasherL≃∙) (inr (y , inr (x , z))))
      where
      p = (cong suc (+-assoc n (suc m) (suc l))
         ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
         ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

      meridLem3 : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
        → subst S₊ (sym (assocPath n m l))
                    (x ⌣S (y ⌣S z))
         ≡ -S^ deg (y ⌣S (x ⌣S z))
      meridLem3 x y z =
         cong (λ P → subst S₊ P (x ⌣S (y ⌣S z)))
              (isSetℕ _ _ _ _)
       ∙ fromPathP
          (compPathP' {B = S₊}
          (compPathP' {B = S₊}
            (λ i → (assoc⌣S x y z i))
            (λ i → 
               (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
                       (sym (comm⌣S x y)) (~ i) ⌣S z))
          ▷ ((⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
                  ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))))
         (λ i → -S^ deg (assoc⌣S y x z (~ i))))

  final-lemma : suspFun∙
      ((λ x → fst (fst tripleSmasherL≃∙) (-S^ deg x)) ∘
       subst S₊ (λ i → assocPath n m l (~ i)))
      ≡
      suspFun∙
      ((inv SmashAssocIso ∘
        (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l))) ∘ fun SmashAssocIso)
       ∘ invEq (invEquiv (fst tripleSmasherL≃∙)))
  final-lemma = ΣPathP ((
    funExt (λ { north → refl
              ; south → refl
              ; (merid a i) j → meridLem1 a j i}))
    , refl)


  s1 = subst∙ (S₊∙ ∘ (2 +_)) (+-assoc n (suc m) (suc l))
  s2 = subst∙ (S₊∙ ∘ suc) (sym (assocPath n m l))

  hoo : (a : S₊ (suc (n + (suc m + suc l))))
    → cong (suspFun (fst (fst tripleSmasherR≃∙)) ∘ fst s1)
           (merid a)
    ≡ merid (fun SmashAssocIso (invEq (fst (invEquiv∙ tripleSmasherL≃∙)) a))
  hoo a = (λ j i → suspFun (fst (fst tripleSmasherR≃∙))
                     (transp (λ i → S₊ (suc (suc
                       (+-assoc n (suc m) (suc l) (i ∨ j))))) j
                     (merid (transp (λ i → S₊ (suc
                       (+-assoc n (suc m) (suc l) (i ∧ j))))
                                    (~ j) a) i)))
        ∙ cong (merid ∘ fst (fst tripleSmasherR≃∙)
              ∘ subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l)))
             (sym (retEq (fst tripleSmasherL≃∙) a))
        ∙ lem2 (fst (fst tripleSmasherL≃∙) a)
    where
    lem2 : (a : _) → merid (fst (fst tripleSmasherR≃∙)
                             (subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l))
                               (invEq (fst tripleSmasherL≃∙) a)))
                    ≡ merid (fun SmashAssocIso a)
    lem2 = ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
            λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
              λ y z →
       cong merid (cong (fst (fst tripleSmasherR≃∙))
                        (fromPathP (assoc⌣S x y z))
                ∙ secEq (fst tripleSmasherR≃∙) (inr (inr (x , y) , z)))


jacobiPath₁ : (p q r : ℕ)
  → suc (suc (q + suc (r + suc p))) ≡
      suc (suc (p + suc (q + suc r)))
jacobiPath₁ p q r =
  cong suc
    (+-assoc (suc q) (suc r) (suc p)
    ∙ sym (+-comm (suc p) (suc q + suc r)))

jacobiPath₂ : (p q r : ℕ)
  → suc (suc (r + suc (p + suc q)))
   ≡ suc (suc (p + suc (q + suc r)))
jacobiPath₂ p q r = cong suc
  (+-comm (suc r) (suc p + suc q)
  ∙ sym (+-assoc (suc p) (suc q) (suc r)))

open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Properties

{-
(p ·₋₁ r + r ·₋₁ (p + suc q)) [ h ∣ [ f ∣ g ]π' ]π')
      (-π^ (r ·₋₁ q) 
-}

open import Cubical.Algebra.Group
-iter-odd+even : ∀ {ℓ} (G : Group ℓ) (n m : ℕ) (g : fst G)
  → isEvenT n ≡ isOddT m
  → GroupStr._·_ (snd G)
      (iter n (GroupStr.inv (snd G)) g)
      (iter m (GroupStr.inv (snd G)) g)
   ≡ GroupStr.1g (snd G)
-iter-odd+even G n m g p with (evenOrOdd n)
... | inl q = cong₂ (GroupStr._·_ (snd G))
                    (iterEvenInv (GroupStr.inv (snd G))
                      (GroupTheory.invInv G) n q g)
                    (iterOddInv (GroupStr.inv (snd G))
                      (GroupTheory.invInv G) m (transport p q) g)
            ∙ GroupStr.·InvR (snd G) g
... | inr q = cong₂ (GroupStr._·_ (snd G))
                    (iterOddInv (GroupStr.inv (snd G))
                      (GroupTheory.invInv G) n q g)
                    (iterEvenInv (GroupStr.inv (snd G))
                      (GroupTheory.invInv G) m
                        (transport (even≡oddFlip n m p) q) g)
            ∙ GroupStr.·InvL (snd G) g

[_∣_]π'Jacobi' : ∀ {ℓ} {X : Pointed ℓ} {p q r : ℕ}
  (f : π' (suc (suc p)) X)
  (g : π' (suc (suc q)) X)
  (h : π' (suc (suc r)) X)
  → ·π' _ (-π^ (p ·₋₁ r) [ f ∣ [ g ∣ h ]π' ]π')
      (·π' _ (subst (λ n → π' n X) (jacobiPath₁ p q r)
                  (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))
             (subst (λ n → π' n X) (jacobiPath₂ p q r)
                    (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π')))
   ≡ 1π' _
[_∣_]π'Jacobi' {X = X} {p} {q} {r} f g h =
  cong₂ _⋄_
        (cong (-π^ (p ·₋₁ r))
              ([_∣_]π'Jacobi f g h)
        ∙ AbGroupTheory.inv^Distr πX _ _ (p ·₋₁ r)
        ∙ λ _ → t1 ⋄ t2)
        (π'-comm _ t3 t4)
      ∙ comm-4 t1 t2 t4 t3
      ∙ cong₂ _⋄_ t1+t4≡0 t2+t3≡0
      ∙ π'-rUnit _ (1π' (suc (suc (p + suc (q + suc r)))))
  where
  πX : AbGroup _
  πX = Group→AbGroup (π'Gr ((suc p) + (suc q + suc r)) X)
                     (π'-comm _)

  open AbGroupTheory πX
  open GroupTheory (π'Gr ((suc p) + (suc q + suc r)) X)
  open AbGroupStr (snd πX) renaming (_+_ to _⋄_ ; -_ to -πX)

  t1 = -π^ (p ·₋₁ r)
         (subst (λ n → π' n X)
                (cong (2 +_) (sym (+-assoc p (suc q) (suc r))))
         [ [ f ∣ g ]π' ∣ h ]π')

  t2 = -π^ (p ·₋₁ r)
         (subst (λ k → π' k X) (cong suc (assocPath p q r))
          (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π'))

  t3 = (subst (λ n → π' n X) (jacobiPath₁ p q r)
                  (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))

  t4 = (subst (λ n → π' n X) (jacobiPath₂ p q r)
                    (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π'))

  -π^-substComm : {n m : ℕ} (t : ℕ) (x : π' (suc n) X) (p : suc n ≡ suc m)
    → -π^ t (subst (λ k → π' k X) p x)
     ≡ subst (λ k → π' k X) p (-π^ t x)
  -π^-substComm t x p =
    cong (λ p → -π^ t (subst (λ k → π' k X) p x)) (isSetℕ _ _ p _)
    ∙ sym (substCommSlice (λ k → π' (suc k) X) (λ k → π' (suc k) X)
            (λ k → -π^ t) (cong predℕ p) x)
    ∙ cong (λ p → subst (λ k → π' k X) p (-π^ t x)) (isSetℕ _ _ _ p)

  t2≡ : -π^ (p ·₋₁ r)
        (subst (λ k → π' k X) (cong suc (assocPath p q r))
         (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π'))
      ≡ subst (λ k → π' k X) (jacobiPath₁ p q r)
           (-π^ (suc p · suc q)
             [ g ∣ [ h ∣ f ]π' ]π')
  t2≡ = -π^-substComm (p ·₋₁ r)
          (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π')
          (cong suc (assocPath p q r))
      ∙ cong (subst (λ k → π' (suc k) X) (assocPath p q r))
             ((sym (iter+ (p ·₋₁ r) (suc p · suc q) (-π' _)
                   [ g ∣ [ f ∣ h ]π' ]π')
             ∙ cong (λ t → -π^ t [ g ∣ [ f ∣ h ]π' ]π')
                    (+-comm (p ·₋₁ r) (suc p · suc q)
                    ∙ cong ((suc p · suc q) +_)
                           (cong suc (·-comm (suc p) (suc r))))
             ∙ iter+ (suc p · suc q) (r ·₋₁ p) (-π' _)
                   [ g ∣ [ f ∣ h ]π' ]π'
             ∙ cong (-π^ (suc p · suc q))
                 ((cong (-π^ (r ·₋₁ p))
                    ((cong [ g ∣_]π' ([_∣_]π'-comm f h)
                   ∙ sym (substCommSlice (λ m → π' (suc m) X)
                                     (λ a → π' (suc (suc q + a)) X)
                                     (λ _ f → [ g ∣ f ]π')
                                     (+-comm (suc r) (suc p))
                                     (-π^ (r ·₋₁ p) [ h ∣ f ]π')))
                   ∙ cong (subst (λ a → π' (suc (suc q + a)) X)
                                 (+-comm (suc r) (suc p)))
                          ([∣]π'-inv^DistrR (r ·₋₁ p) g [ h ∣ f ]π'))
                 ∙ -π^-substComm (r ·₋₁ p) (-π^ (r ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π')
                     (λ i → suc (suc q + +-comm (suc r) (suc p) i))
                 ∙ cong (subst (λ k → π' k X)
                               (λ i → suc (suc q + +-comm (suc r) (suc p) i)))
                        (iter+iter (-π' _) (GroupTheory.invInv (π'Gr _ _))
                         (r ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π')))
             ∙ -π^-substComm (suc p · suc q) ([ g ∣ [ h ∣ f ]π' ]π')
                             (λ i → suc (suc q + +-comm (suc r) (suc p) i)))
            ∙ refl)
      ∙ compSubstℕ {A = λ n → π' n X}
          (λ i → suc (suc q + +-comm (suc r) (suc p) i))
          (cong suc (assocPath p q r))
          (jacobiPath₁ p q r)
          {(-π^ (suc p · suc q) [ g ∣ [ h ∣ f ]π' ]π')}

  t1≡ : t1 ≡ subst (λ n → π' n X) (jacobiPath₂ p q r)
                   (-π^ (p ·₋₁ r + r ·₋₁ (p + suc q))
                   [ h ∣ [ f ∣ g ]π' ]π')
  t1≡ = cong (-π^ (p ·₋₁ r)
         ∘ subst (λ n → π' n X)
                (cong (2 +_) (sym (+-assoc p (suc q) (suc r)))))
             ([_∣_]π'-comm ([ f ∣ g ]π') h)
      ∙ cong (-π^ (p ·₋₁ r))
             (compSubstℕ {A = λ n → π' n X}
               (cong suc (+-comm (suc r) (suc (p + suc q))))
               (sym (cong suc (+-assoc (suc p) (suc q) (suc r))))
               (jacobiPath₂ p q r))
      ∙ sym (substCommSlice
            (λ k → π' (suc k) X) (λ k → π' (suc k) X)
            (λ k → -π^ (p ·₋₁ r))
            (cong predℕ (jacobiPath₂ p q r))
            _)
      ∙ cong (subst (λ n → π' n X) (jacobiPath₂ p q r))
             (sym (iter+ (p ·₋₁ r) (r ·₋₁ (p + suc q)) (-π' _)
                     ([ h ∣ [ f ∣ g ]π' ]π'))
            ∙ refl)

  substHomLem : (n m : ℕ) (p : n ≡ m) {x y : π' (suc n) X}
    → ·π' _ (subst (λ n → π' (suc n) X) p x) (subst (λ n → π' (suc n) X) p y)
     ≡ subst (λ n → π' (suc n) X) p (·π' _ x y)
  substHomLem n = J> λ {x y} →
      cong₂ (·π' _) (transportRefl x) (transportRefl y)
    ∙ sym (transportRefl (·π' n x y))

  t1+t4≡0 : t1 ⋄ t4 ≡ 1π' _
  t1+t4≡0 = cong₂ _⋄_ t1≡ refl
          ∙ substHomLem _ _ (cong predℕ (jacobiPath₂ p q r))
          ∙ cong (subst (λ n → π' n X) (jacobiPath₂ p q r))
                 ((λ _ →
                   ·π' _ (-π^ (p ·₋₁ r + r ·₋₁ (p + suc q))
                              [ h ∣ [ f ∣ g ]π' ]π')
                         (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π'))
               ∙ -iter-odd+even (π'Gr (suc (r + suc (p + suc q))) X)
                   (suc (suc (r + p · suc r + r ·₋₁ (p + suc q))))
                   (r ·₋₁ q) ([ h ∣ [ f ∣ g ]π' ]π') (evenOddLemma1' p q r))
          ∙ λ j → transp (λ i → π' (jacobiPath₂ p q r (i ∨ j)) X) j
                    (1π' (jacobiPath₂ p q r j))

  t2+t3≡0 : t2 ⋄ t3 ≡ 1π' _
  t2+t3≡0 =
      cong₂ _⋄_ t2≡ refl
    ∙ substHomLem _ _ (cong predℕ (jacobiPath₁ p q r))
    ∙ cong (subst (λ n → π' n X) (jacobiPath₁ p q r))
           ((λ _ → ·π' _ (-π^ (suc p · suc q) [ g ∣ [ h ∣ f ]π' ]π')
                          (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))
          ∙ -iter-odd+even (π'Gr (suc (q + suc (r + suc p))) X) (suc p · suc q) (q ·₋₁ p)
                           [ g ∣ [ h ∣ f ]π' ]π' (cong isEvenT (·-comm (suc p) (suc q))))
    ∙ λ j → transp (λ i → π' (jacobiPath₁ p q r (i ∨ j)) X) j
                    (1π' (jacobiPath₁ p q r j))
