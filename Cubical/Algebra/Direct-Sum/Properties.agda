{-# OPTIONS --safe #-}
module Cubical.Algebra.Direct-Sum.Properties where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat renaming(_+_ to _+n_)
open import Cubical.Data.Int renaming(_+_ to _+z_; -_ to -z; _·_ to _·z_ )
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing



open import Cubical.Algebra.Direct-Sum.Base

private variable
  l l' : Level

module _ (I : Type l) (P : I → Type l) (AGP : (r : I) → AbGroupStr (P r)) where
  
  inv : ⊕ I P AGP → ⊕ I P AGP
  inv = DS-Rec-Set.f I P AGP (⊕ I P AGP) trunc
           -- elements
           neutral
           (λ r a → base r (AbGroupStr.-_ (AGP r) a))
           (λ xs ys → xs add ys)
           -- eq group
           (λ xs ys zs → add-assoc xs ys zs)
           (λ xs → add-neutral xs)
           (λ xs ys → add-com xs ys)
           -- eq base
           (λ r → let open AbGroupStr (AGP r) in
                   let open GroupTheory (P r , AbGroupStr→GroupStr (AGP r)) in
                   (cong (base r) inv1g) ∙ (base-neutral r))
           (λ r a b → let open AbGroupStr (AGP r) in
                       let open GroupTheory (P r , AbGroupStr→GroupStr (AGP r)) in
                       ((base r (- a) add base r (- b))   ≡⟨ (base-add r (- a) (- b)) ⟩
                       base r ((- a) + (- b))             ≡⟨ (cong (base r) (sym (invDistr b a))) ⟩
                       base r (- (b + a))                 ≡⟨ cong (base r) (cong (-_) (comm b a)) ⟩
                       base r (- (a + b)) ∎))



  rinv : (z : ⊕ I P AGP) → z add (inv z) ≡ neutral
  rinv = DS-Ind-Prop.f I P AGP (λ z → z add (inv z) ≡ neutral) (λ _ → trunc _ _) 
         -- elements
         (add-neutral neutral)
         (λ r a → let open AbGroupStr (AGP r) in
                        ((base r a add base r (- a)) ≡⟨ base-add r a (- a) ⟩
                        base r (a + - a)             ≡⟨ cong (base r) (invr a) ⟩
                        base r 0g                    ≡⟨ base-neutral r ⟩
                        neutral ∎))
         (λ {x} {y} p q →
                        (((x add y) add ((inv x) add (inv y)))   ≡⟨ cong (λ X → X add ((inv x) add (inv y))) (add-com x y) ⟩
                        ((y add x) add (inv x add inv y))        ≡⟨ sym (add-assoc y x (inv x add inv y)) ⟩
                        (y add (x add (inv x add inv y)))        ≡⟨ cong (λ X → y add X) (add-assoc x (inv x) (inv y)) ⟩
                        (y add ((x add inv x) add inv y))        ≡⟨ cong (λ X → y add (X add (inv y))) (p) ⟩
                        (y add (neutral add inv y))              ≡⟨ cong (λ X → y add X) (add-com neutral (inv y)) ⟩
                        (y add (inv y add neutral))              ≡⟨ cong (λ X → y add X) (add-neutral (inv y)) ⟩
                        (y add inv y)                            ≡⟨ q ⟩
                        neutral ∎))


  DS-com-adv : (x y z w : ⊕ I P AGP) →  ((x add y) add (z add w) ≡ (x add z) add (y add w))
  DS-com-adv x y z w = ((x add y) add (z add w) ≡⟨ add-assoc (x add y) z w ⟩
                       (((x add y) add z) add w) ≡⟨ cong (λ X → X add w) (sym (add-assoc x y z)) ⟩
                       ((x add (y add z)) add w) ≡⟨ cong (λ X → (x add X) add w) (add-com y z) ⟩
                       ((x add (z add y)) add w) ≡⟨ cong (λ X → X add w) (add-assoc x z y) ⟩
                       (((x add z) add y) add w) ≡⟨ sym (add-assoc (x add z) y w) ⟩
                       ((x add z) add (y add w)) ∎)
       

  open AbGroupStr
  open IsAbGroup
  open IsGroup 
  open IsMonoid
  open IsSemigroup
  -- open isAbGroup

  ⊕-AbGr : AbGroup l
  fst ⊕-AbGr = ⊕ I P AGP
  0g (snd ⊕-AbGr) = neutral
  _+_ (snd ⊕-AbGr) = _add_
  - snd ⊕-AbGr = inv
  isAbGroup (snd ⊕-AbGr) = makeIsAbGroup trunc add-assoc add-neutral rinv add-com
 
  

