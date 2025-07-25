module Cubical.Algebra.DirectSum.DirectSumHIT.Base where

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


data ⊕HIT (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) : Type (ℓ-max ℓ ℓ')  where
  -- elements
  neutral      : ⊕HIT Idx P AGP
  base         : (r : Idx) → (P r) → ⊕HIT Idx P AGP
  _add_        : ⊕HIT Idx P AGP → ⊕HIT Idx P AGP → ⊕HIT Idx P AGP
  -- eq group
  addAssoc     : (x y z : ⊕HIT Idx P AGP) → x add (y add z) ≡ (x add y) add z
  addRid       : (x : ⊕HIT Idx P AGP)     → x add neutral ≡ x
  addComm      : (x y : ⊕HIT Idx P AGP)   → x add y ≡ y add x
  -- eq base
  base-neutral : (r : Idx)                → base r (AbGroupStr.0g (AGP r)) ≡ neutral
  base-add     : (r : Idx) → (a b : P r) → (base r a) add (base r b) ≡ base r (AbGroupStr._+_ (AGP r) a b)
  -- set
  trunc        : isSet (⊕HIT Idx P AGP)



module _ (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) where

  module DS-Ind-Set
    (Q            : (x : ⊕HIT Idx P AGP) → Type ℓ'')
    (issd         : (x : ⊕HIT Idx P AGP) → isSet (Q x))
    -- elements
    (neutral*     : Q neutral)
    (base*        : (r : Idx) → (a : P r) → Q (base r a))
    (_add*_       : {x y : ⊕HIT Idx P AGP} → Q x → Q y → Q (x add y))
    -- eq group
    (addAssoc*    : {x y z : ⊕HIT Idx P AGP} → (xs : Q x) → (ys : Q y) → (zs : Q z)
                    → PathP ( λ i →  Q ( addAssoc x y z i)) (xs add* (ys add* zs)) ((xs add* ys) add* zs))
    (addRid*      : {x : ⊕HIT Idx P AGP} → (xs : Q x)
                    → PathP (λ i → Q (addRid x i)) (xs add* neutral*) xs )
    (addComm*     : {x y : ⊕HIT Idx P AGP} → (xs : Q x) → (ys : Q y)
                    → PathP (λ i → Q (addComm x y i)) (xs add* ys) (ys add* xs))
    -- -- eq base
    (base-neutral* : (r : Idx)
                     → PathP (λ i → Q (base-neutral r i)) (base* r (AbGroupStr.0g (AGP r))) neutral*)
    (base-add*     : (r : Idx) → (a b : P r)
                     → PathP (λ i → Q (base-add r a b i)) ((base* r a) add* (base* r b)) (base* r (AbGroupStr._+_ (AGP r) a b)))
    where

    f : (x : ⊕HIT Idx P AGP) → Q x
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

    f : ⊕HIT Idx P AGP → B
    f z = DS-Ind-Set.f (λ _ → B) (λ _ → iss) neutral* base* _add*_ addAssoc* addRid* addComm* base-neutral* base-add* z



  module DS-Ind-Prop
    (Q            : (x : ⊕HIT Idx P AGP) → Type ℓ'')
    (isPropQ      : (x : ⊕HIT Idx P AGP) → isProp (Q x))
    -- elements
    (neutral*     : Q neutral)
    (base*        : (r : Idx) → (a : P r) → Q (base r a))
    (_add*_       : {x y : ⊕HIT Idx P AGP} → Q x → Q y → Q (x add y))
    where

    f : (x : ⊕HIT Idx P AGP) → Q x
    f x = DS-Ind-Set.f Q (λ x → isProp→isSet (isPropQ x)) neutral* base* _add*_
          (λ {x} {y} {z} xs ys zs → toPathP (isPropQ _ (transport (λ i → Q (addAssoc x y z i)) (xs add* (ys add* zs))) ((xs add* ys) add* zs)))
          (λ {x} xs               → toPathP (isPropQ _ (transport (λ i → Q (addRid x i))       (xs add* neutral*)) xs))
          (λ {x} {y} xs ys        → toPathP (isPropQ _ (transport (λ i → Q (addComm x y i))    (xs add* ys)) (ys add* xs)))
          (λ r                    → toPathP (isPropQ _ (transport (λ i → Q (base-neutral r i)) (base* r (AbGroupStr.0g (AGP r)))) neutral*))
          (λ r a b                → toPathP (isPropQ _ (transport (λ i → Q (base-add r a b i)) ((base* r a) add* (base* r b))) (base* r (AbGroupStr._+_ (AGP r) a b)  )))
          x


  module DS-Rec-Prop
    (B        : Type ℓ'')
    (isp      : isProp B)
    (neutral* : B)
    (base*    : (r : Idx) → P r → B)
    (_add*_   : B → B → B)
    where

    f : ⊕HIT Idx P AGP → B
    f x = DS-Ind-Prop.f (λ _ → B) (λ _ → isp) neutral* base* _add*_ x
