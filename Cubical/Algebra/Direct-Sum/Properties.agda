{-# OPTIONS --safe #-}
module Cubical.Algebra.Direct-Sum.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup

open import Cubical.Algebra.Direct-Sum.Base

private variable
  ℓ ℓ' : Level

module _ (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) where

  inv : ⊕ Idx P AGP → ⊕ Idx P AGP
  inv = DS-Rec-Set.f Idx P AGP (⊕ Idx P AGP) trunc
           -- elements
           neutral
           (λ r a → base r (AbGroupStr.-_ (AGP r) a))
           (λ xs ys → xs add ys)
           -- eq group
           (λ xs ys zs → addAssoc xs ys zs)
           (λ xs → addRid xs)
           (λ xs ys → addComm xs ys)
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



  rinv : (z : ⊕ Idx P AGP) → z add (inv z) ≡ neutral
  rinv = DS-Ind-Prop.f Idx P AGP (λ z → z add (inv z) ≡ neutral) (λ _ → trunc _ _)
         -- elements
         (addRid neutral)
         (λ r a → let open AbGroupStr (AGP r) in
                        ((base r a add base r (- a)) ≡⟨ base-add r a (- a) ⟩
                        base r (a + - a)             ≡⟨ cong (base r) (invr a) ⟩
                        base r 0g                    ≡⟨ base-neutral r ⟩
                        neutral ∎))
         (λ {x} {y} p q →
                        (((x add y) add ((inv x) add (inv y)))   ≡⟨ cong (λ X → X add ((inv x) add (inv y))) (addComm x y) ⟩
                        ((y add x) add (inv x add inv y))        ≡⟨ sym (addAssoc y x (inv x add inv y)) ⟩
                        (y add (x add (inv x add inv y)))        ≡⟨ cong (λ X → y add X) (addAssoc x (inv x) (inv y)) ⟩
                        (y add ((x add inv x) add inv y))        ≡⟨ cong (λ X → y add (X add (inv y))) (p) ⟩
                        (y add (neutral add inv y))              ≡⟨ cong (λ X → y add X) (addComm neutral (inv y)) ⟩
                        (y add (inv y add neutral))              ≡⟨ cong (λ X → y add X) (addRid (inv y)) ⟩
                        (y add inv y)                            ≡⟨ q ⟩
                        neutral ∎))
