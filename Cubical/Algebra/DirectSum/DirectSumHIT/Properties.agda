{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.DirectSumHIT.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base

private variable
  ℓ ℓ' : Level

module AbGroupProperties
  (Idx : Type ℓ)
  (P : Idx → Type ℓ')
  (AGP : (r : Idx) → AbGroupStr (P r))
  where

  inv : ⊕HIT Idx P AGP → ⊕HIT Idx P AGP
  inv = DS-Rec-Set.f Idx P AGP (⊕HIT Idx P AGP) trunc
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
                       base r (- (b + a))                 ≡⟨ cong (base r) (cong (-_) (+Comm b a)) ⟩
                       base r (- (a + b)) ∎))



  rinv : (z : ⊕HIT Idx P AGP) → z add (inv z) ≡ neutral
  rinv = DS-Ind-Prop.f Idx P AGP (λ z → z add (inv z) ≡ neutral) (λ _ → trunc _ _)
         -- elements
         (addRid neutral)
         (λ r a → let open AbGroupStr (AGP r) in
                        ((base r a add base r (- a)) ≡⟨ base-add r a (- a) ⟩
                        base r (a + - a)             ≡⟨ cong (base r) (+InvR a) ⟩
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

module SubstLemma
  (Idx : Type ℓ)
  (G    : Idx → Type ℓ')
  (Gstr : (r : Idx) → AbGroupStr (G r))
  where

  open AbGroupStr

  substG : {k l : Idx} → (x : k ≡ l) → (a : G k) → G l
  substG x a = subst G x a

  substG0 : {k l : Idx} → (p : k ≡ l) → subst G p (0g (Gstr k)) ≡ 0g (Gstr l)
  substG0 {k} {l} p = J (λ l p → subst G p (0g (Gstr k)) ≡ 0g (Gstr l)) (transportRefl _) p

  substG+ : {k : Idx} → (a b : G k) → {l : Idx} →  (p : k ≡ l) →
           Gstr l ._+_ (subst G p a) (subst G p b) ≡ subst G p (Gstr k ._+_ a b)
  substG+ {k} a b {l} p = J (λ l p → Gstr l ._+_ (subst G p a) (subst G p b) ≡ subst G p (Gstr k ._+_ a b))
                         (cong₂ (Gstr k ._+_) (transportRefl _) (transportRefl _) ∙ sym (transportRefl _))
                         p



module DecIndec-BaseProperties
  (Idx  : Type ℓ)
  (decIdx : Discrete Idx)
  (G    : Idx → Type ℓ')
  (Gstr : (r : Idx) → AbGroupStr (G r))
  where

  open AbGroupStr
  open SubstLemma Idx G Gstr

  πₖ : (k : Idx) → ⊕HIT Idx G Gstr → G k
  πₖ k = DS-Rec-Set.f _ _ _ _ (is-set (Gstr k))
         (0g (Gstr k))
         base-trad
         (_+_ (Gstr k))
         (+Assoc (Gstr k))
         (+IdR (Gstr k))
         (+Comm (Gstr k))
         base-neutral-eq
         base-add-eq
     where
     base-trad : (l : Idx) → (a : G l) → G k
     base-trad l a with decIdx l k
     ... | yes p = subst G p a
     ... | no ¬p = 0g (Gstr k)

     base-neutral-eq : _
     base-neutral-eq l with decIdx l k
     ... | yes p = substG0 p
     ... | no ¬p = refl

     base-add-eq : _
     base-add-eq l a b with decIdx l k
     ... | yes p = substG+ a b p
     ... | no ¬p = +IdR (Gstr k) _

  πₖ-id : {k : Idx} → (a : G k) → πₖ k (base k a) ≡ a
  πₖ-id {k} a with decIdx k k
  ... | yes p = cong (λ X → subst G X a) (Discrete→isSet decIdx _ _ _ _) ∙ transportRefl _
  ... | no ¬p = rec (¬p refl)

  πₖ-0g : {k l : Idx} → (a : G l) → (p : k ≡ l → ⊥) → πₖ k (base l a) ≡ 0g (Gstr k)
  πₖ-0g {k} {l} a ¬q with decIdx l k
  ... | yes p = rec (¬q (sym p))
  ... | no ¬p = refl

  base-inj : {k : Idx} → {a b : G k} → base {AGP = Gstr} k a ≡ base k b → a ≡ b
  base-inj {k} {a} {b} p = sym (πₖ-id a) ∙ cong (πₖ k) p ∙ πₖ-id b

  base-≢ : {k : Idx} → {a : G k} → {l : Idx} → {b : G l} → (p : k ≡ l → ⊥) →
           base {AGP = Gstr} k a ≡ base {AGP = Gstr} l b → (a ≡ 0g (Gstr k)) × (b ≡ 0g (Gstr l))
  base-≢ {k} {a} {l} {b} ¬p q = helper1 , helper2
    where
    helper1 : a ≡ 0g (Gstr k)
    helper1 = sym (πₖ-id a) ∙ cong (πₖ k) q ∙ πₖ-0g b ¬p

    helper2 : b ≡ 0g (Gstr l)
    helper2 = sym (πₖ-id b) ∙ cong (πₖ l) (sym q) ∙ πₖ-0g a (λ x → ¬p (sym x))
