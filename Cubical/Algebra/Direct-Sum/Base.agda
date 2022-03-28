{-# OPTIONS --safe #-}
module Cubical.Algebra.Direct-Sum.Base where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat renaming(_+_ to _+n_)
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup


-- Conventions :
-- Elements of the index are named r, s, t...
-- Elements of the groups are called a, b, c...
-- Elements of the direct sum are named x, y, z...
-- Elements in the fiber of Q x, Q y are called xs, ys...


private variable
  l l' : Level


data ⊕ (I : Type l) (P : I → Type l) (AGP : (r : I) → AbGroupStr (P r)) : Type l  where
  -- elements
  neutral      : ⊕ I P AGP
  base         : (r : I) → (P r) → ⊕ I P AGP
  _add_        : ⊕ I P AGP → ⊕ I P AGP → ⊕ I P AGP 
  -- eq group
  add-assoc    : (x y z : ⊕ I P AGP) → x add (y add z) ≡ (x add y) add z
  add-neutral  : (x : ⊕ I P AGP)     → x add neutral ≡ x
  add-com      : (x y : ⊕ I P AGP)   → x add y ≡ y add x 
  -- eq base 
  base-neutral : (r : I) → base r (AbGroupStr.0g (AGP r)) ≡ neutral
  base-add     : (r : I) → (a b : P r) → (base r a) add (base r b) ≡ base r (AbGroupStr._+_ (AGP r) a b)
  -- set
  trunc        : isSet (⊕ I P AGP) 

  

module _ (I : Type l) (P : I → Type l) (AGP : (r : I) → AbGroupStr (P r)) where

  module DS-Ind-Set 
    (Q            : (x : ⊕ I P AGP) → Type l')
    (issd         : (x : ⊕ I P AGP) → isSet (Q x))
    -- elements
    (ne           : Q neutral)
    (nb           : (r : I) → (a : P r) → Q (base r a))
    (_na_         : {x y : ⊕ I P AGP} → Q x → Q y → Q (x add y)) 
    -- eq group
    (add-assoc*   : {x y z : ⊕ I P AGP} → (xs : Q x) → (ys : Q y) → (zs : Q z)
                  → PathP ( λ i →  Q ( add-assoc x y z i)) (xs na (ys na zs)) ((xs na ys) na zs))
    (add-neutral* : {x : ⊕ I P AGP} → (xs : Q x) →
                    PathP (λ i → Q (add-neutral x i)) (xs na ne) xs ) 
    (add-com*     : {x y : ⊕ I P AGP} → (xs : Q x) → (ys : Q y)
                    → PathP (λ i → Q (add-com x y i)) (xs na ys) (ys na xs)) 
    -- -- eq base
    (base-neutral* : (r : I) →
                     PathP (λ i → Q (base-neutral r i)) (nb r (AbGroupStr.0g (AGP r))) ne) 
    (base-add*     : (r : I) → (a b : P r) →
                    PathP (λ i → Q (base-add r a b i)) ((nb r a) na (nb r b)) (nb r (AbGroupStr._+_ (AGP r) a b)))
    where

    f : (x : ⊕ I P AGP) → Q x
    f neutral    = ne
    f (base r a) = nb r a
    f (x add y)  = (f x) na (f y)
    f (add-assoc x y z i) = add-assoc* (f x) (f y) (f z) i
    f (add-neutral x i)   = add-neutral* (f x) i
    f (add-com x y i)     = add-com* (f x) (f y) i
    f (base-neutral r i)  = base-neutral* r i
    f (base-add r a b i)  = base-add* r a b i
    f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (issd)  (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i j


  module DS-Rec-Set
    (B : Type l')
    (iss : isSet(B))
    (ne : B)
    (nb : (r : I) → P r → B)
    (_na_ : B → B → B)
    (add-assoc* : (xs ys zs : B) → (xs na (ys na zs)) ≡ ((xs na ys) na zs))
    (add-neutral* : (xs : B) → xs na ne ≡ xs)
    (add-com* : (xs ys : B) → xs na ys ≡ ys na xs)
    (base-neutral* : (r : I) → nb r (AbGroupStr.0g (AGP r)) ≡ ne)
    (base-add* : (r : I) → (a b : P r) → (nb r a) na (nb r b) ≡ nb r (AbGroupStr._+_ (AGP r) a b)) 
    where

    f : ⊕ I P AGP → B
    f z = DS-Ind-Set.f (λ _ → B) (λ _ → iss) ne nb _na_ add-assoc* add-neutral* add-com* base-neutral* base-add* z



  module DS-Ind-Prop 
    (Q            : (x : ⊕ I P AGP) → Type l')
    (ispd         : (x : ⊕ I P AGP) → isProp (Q x))
    -- elements
    (ne           : Q neutral)
    (nb           : (r : I) → (a : P r) → Q (base r a))
    (_na_         : {x y : ⊕ I P AGP} → Q x → Q y → Q (x add y))
    where

    f : (x : ⊕ I P AGP) → Q x
    f x = DS-Ind-Set.f Q (λ x → isProp→isSet (ispd x)) ne nb _na_
          (λ {x} {y} {z} xs ys zs → toPathP (ispd _ (transport (λ i → Q (add-assoc x y z i)) (xs na (ys na zs))) ((xs na ys) na zs)))
          (λ {x} xs               → toPathP (ispd _ (transport (λ i → Q (add-neutral x i))   (xs na ne)) xs))
          (λ {x} {y} xs ys        → toPathP (ispd _ (transport (λ i → Q (add-com x y i))     (xs na ys)) (ys na xs)))
          (λ r                    → toPathP (ispd _ (transport (λ i → Q (base-neutral r i))  (nb r (AbGroupStr.0g (AGP r)))) ne))
          (λ r a b                → toPathP (ispd _ (transport (λ i → Q (base-add r a b i))  ((nb r a) na (nb r b))) (nb r (AbGroupStr._+_ (AGP r) a b)  )))
          x


  module DS-Rec-Prop 
    (B : Type l')
    (isp : isProp B)
    (ne : B)
    (nb : (r : I) → P r → B)
    (_na_ : B → B → B)
    where

    f : ⊕ I P AGP → B
    f x = DS-Ind-Prop.f (λ _ → B) (λ _ → isp) ne nb _na_ x


