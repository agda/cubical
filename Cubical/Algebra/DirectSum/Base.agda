{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.AbGroup


-- Conventions :
-- Elements of the index are named r, s, t...
-- Elements of the groups are called a, b, c...
-- Elements of the direct sum are named x, y, z...
-- Elements in the fiber of Q x, Q y are called xs, ys...


private variable
  ℓ ℓ' ℓ'' : Level


data ⊕ (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) : Type (ℓ-max ℓ ℓ')  where
  -- elements
  neutral      : ⊕ Idx P AGP
  base         : (r : Idx) → (P r) → ⊕ Idx P AGP
  _add_        : ⊕ Idx P AGP → ⊕ Idx P AGP → ⊕ Idx P AGP
  -- eq group
  addAssoc     : (x y z : ⊕ Idx P AGP) → x add (y add z) ≡ (x add y) add z
  addRid       : (x : ⊕ Idx P AGP)     → x add neutral ≡ x
  addComm      : (x y : ⊕ Idx P AGP)   → x add y ≡ y add x
  -- eq base
  base-neutral : (r : Idx)                → base r (AbGroupStr.0g (AGP r)) ≡ neutral
  base-add     : (r : Idx) → (a b : P r) → (base r a) add (base r b) ≡ base r (AbGroupStr._+_ (AGP r) a b)
  -- set
  trunc        : isSet (⊕ Idx P AGP)

module _ (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) where

  module DS-Ind-Set
    (Q            : (x : ⊕ Idx P AGP) → Type ℓ'')
    (issd         : (x : ⊕ Idx P AGP) → isSet (Q x))
    -- elements
    (neutral*     : Q neutral)
    (base*        : (r : Idx) → (a : P r) → Q (base r a))
    (_add*_       : {x y : ⊕ Idx P AGP} → Q x → Q y → Q (x add y))
    -- eq group
    (addAssoc*    : {x y z : ⊕ Idx P AGP} → (xs : Q x) → (ys : Q y) → (zs : Q z)
                    → PathP ( λ i →  Q ( addAssoc x y z i)) (xs add* (ys add* zs)) ((xs add* ys) add* zs))
    (addRid*      : {x : ⊕ Idx P AGP} → (xs : Q x)
                    → PathP (λ i → Q (addRid x i)) (xs add* neutral*) xs )
    (addComm*     : {x y : ⊕ Idx P AGP} → (xs : Q x) → (ys : Q y)
                    → PathP (λ i → Q (addComm x y i)) (xs add* ys) (ys add* xs))
    -- -- eq base
    (base-neutral* : (r : Idx)
                     → PathP (λ i → Q (base-neutral r i)) (base* r (AbGroupStr.0g (AGP r))) neutral*)
    (base-add*     : (r : Idx) → (a b : P r)
                     → PathP (λ i → Q (base-add r a b i)) ((base* r a) add* (base* r b)) (base* r (AbGroupStr._+_ (AGP r) a b)))
    where

    f : (x : ⊕ Idx P AGP) → Q x
    f neutral    = neutral*
    f (base r a) = base* r a
    f (x add y)  = (f x) add* (f y)
    f (addAssoc x y z i)  = addAssoc* (f x) (f y) (f z) i
    f (addRid x i)        = addRid* (f x) i
    f (addComm x y i)     = addComm* (f x) (f y) i
    f (base-neutral r i)  = base-neutral* r i
    f (base-add r a b i)  = base-add* r a b i
    f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (issd)  (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i j


  module DS-Rec-Set
    (B : Type ℓ'')
    (iss : isSet(B))
    (neutral* : B)
    (base*    : (r : Idx) → P r → B)
    (_add*_   : B → B → B)
    (addAssoc*     : (xs ys zs : B) → (xs add* (ys add* zs)) ≡ ((xs add* ys) add* zs))
    (addRid*       : (xs : B)       → xs add* neutral* ≡ xs)
    (addComm*      : (xs ys : B)    → xs add* ys ≡ ys add* xs)
    (base-neutral* : (r : Idx)                → base* r (AbGroupStr.0g (AGP r)) ≡ neutral*)
    (base-add*     : (r : Idx) → (a b : P r) → (base* r a) add* (base* r b) ≡ base* r (AbGroupStr._+_ (AGP r) a b))
    where

    f : ⊕ Idx P AGP → B
    f z = DS-Ind-Set.f (λ _ → B) (λ _ → iss) neutral* base* _add*_ addAssoc* addRid* addComm* base-neutral* base-add* z



  module DS-Ind-Prop
    (Q            : (x : ⊕ Idx P AGP) → Type ℓ'')
    (ispd         : (x : ⊕ Idx P AGP) → isProp (Q x))
    -- elements
    (neutral*     : Q neutral)
    (base*        : (r : Idx) → (a : P r) → Q (base r a))
    (_add*_       : {x y : ⊕ Idx P AGP} → Q x → Q y → Q (x add y))
    where

    f : (x : ⊕ Idx P AGP) → Q x
    f x = DS-Ind-Set.f Q (λ x → isProp→isSet (ispd x)) neutral* base* _add*_
          (λ {x} {y} {z} xs ys zs → toPathP (ispd _ (transport (λ i → Q (addAssoc x y z i)) (xs add* (ys add* zs))) ((xs add* ys) add* zs)))
          (λ {x} xs               → toPathP (ispd _ (transport (λ i → Q (addRid x i))       (xs add* neutral*)) xs))
          (λ {x} {y} xs ys        → toPathP (ispd _ (transport (λ i → Q (addComm x y i))    (xs add* ys)) (ys add* xs)))
          (λ r                    → toPathP (ispd _ (transport (λ i → Q (base-neutral r i)) (base* r (AbGroupStr.0g (AGP r)))) neutral*))
          (λ r a b                → toPathP (ispd _ (transport (λ i → Q (base-add r a b i)) ((base* r a) add* (base* r b))) (base* r (AbGroupStr._+_ (AGP r) a b)  )))
          x


  module DS-Rec-Prop
    (B        : Type ℓ'')
    (isp      : isProp B)
    (neutral* : B)
    (base*    : (r : Idx) → P r → B)
    (_add*_   : B → B → B)
    where

    f : ⊕ Idx P AGP → B
    f x = DS-Ind-Prop.f (λ _ → B) (λ _ → isp) neutral* base* _add*_ x
{-
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary
module _ (P : ℕ → Type ℓ') (AGP : (r : ℕ) → AbGroupStr (P r)) where
  CodeHelper : (n r : ℕ) → (n ≡ r) ⊎ (¬ n ≡ r) → (a : P n) (b : P r)
    → TypeOfHLevel ℓ' 1
  CodeHelper n r (inl x) a b = (a ≡ subst P (sym x) b) , AbGroupStr.is-set (AGP n) _ _
  CodeHelper n r (inr x) a b = (a ≡ AbGroupStr.0g (AGP n)) × (b ≡ AbGroupStr.0g (AGP r)) , isProp× (AbGroupStr.is-set (AGP n) _ _) (AbGroupStr.is-set (AGP r) _ _)

  decℕ : (n r : ℕ) → (n ≡ r) ⊎ (¬ n ≡ r)
  decℕ zero zero = inl refl
  decℕ zero (suc r) = inr λ p → snotz (sym p)
  decℕ (suc n) zero = inr snotz
  decℕ (suc n) (suc r) = ⊎.rec (λ p → inl (cong suc p)) (λ p → inr λ q → p ( (cong predℕ q))) (decℕ n r)

  propLem : (n r : ℕ) → isProp ((n ≡ r) ⊎ (¬ n ≡ r))
  propLem n r (inl x) (inl y) = {!!}
  propLem n r (inl x) (inr y) = {!!}
  propLem n r (inr x) q = {!!}

  funHelper : (n r : ℕ) → (n ≡ r) ⊎ (¬ n ≡ r) → (b : P r) → P n
  funHelper n r (inl x) b = subst P (sym x) b
  funHelper n r (inr x) b = AbGroupStr.0g (AGP n)

  projmap : (n : ℕ) → ⊕ ℕ P AGP → P n
  projmap n neutral = AbGroupStr.0g (AGP n)
  projmap n (base r x) = funHelper n r (decℕ n r) x
  projmap n (x add x₁) = AbGroupStr._+_ (AGP n) (projmap n x) (projmap n x₁)
  projmap n (addAssoc x y z i) =
    AbGroupStr.assoc (AGP n) (projmap n x) (projmap n y) (projmap n z) i
  projmap n (addRid x i) = AbGroupStr.rid (AGP n) (projmap n x) i
  projmap n (addComm x x₁ i) = AbGroupStr.comm (AGP n) (projmap n x) (projmap n x₁) i
  projmap n (base-neutral r i) = zz (decℕ n r) i
    where
    zz : (p : _) → funHelper n r p (AbGroupStr.0g (AGP r)) ≡ AbGroupStr.0g (AGP n)
    zz (inl x) = J (λ r x → subst P (λ i₁ → x (~ i₁)) (AbGroupStr.0g (AGP r)) ≡ AbGroupStr.0g (AGP n)) (transportRefl _) x
    zz (inr x) = refl
  projmap n (base-add r a b i) = zz2 (decℕ n r) i
    where
    zz2 : (p : _) → AbGroupStr._+_ (AGP n) (funHelper n r p a) (funHelper n r p b)
                                          ≡ funHelper n r p ((AGP r AbGroupStr.+ a) b)
    zz2 (inl x) = J (λ r x → (a b : _) → (AGP n AbGroupStr.+ subst P (λ i₁ → x (~ i₁)) a)
      (subst P (λ i₁ → x (~ i₁)) b)
      ≡ subst P (λ i₁ → x (~ i₁)) ((AGP r AbGroupStr.+ a) b))
        (λ a b → cong₂ (AbGroupStr._+_ (AGP n)) (transportRefl a) (transportRefl b) ∙ sym (transportRefl _)) x a b
    zz2 (inr x) = AbGroupStr.rid (AGP n) (AbGroupStr.0g (AGP n))
  projmap n (trunc x x₁ x₂ y i i₁) =
    AbGroupStr.is-set (AGP n) (projmap n x) (projmap n x₁) (cong (projmap n) x₂) (cong (projmap n) y) i i₁

  lemm : (i j : ℕ) → (¬ i ≡ j)
       → (a : P i) (b : P j) → Path (⊕ ℕ P AGP) (base i a) (base j b)
       → (a ≡ AbGroupStr.0g (AGP i))
        × (b ≡ AbGroupStr.0g (AGP j))
  fst (lemm i j p a b q) =
    (sym (transportRefl a) ∙ (λ k → funHelper i i (propLem i i (decℕ i i) (inl refl) (~ k)) a)) ∙∙ cong (projmap i) q ∙∙ ((λ k → funHelper i j (propLem i j (decℕ i j) (inr p) k) b))
  snd (lemm i j p a b q) = {!!}
-}
