-- TODO: uncomment once finished!
-- {-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData hiding (_==_ ; snotz)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base hiding (map)

open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-rec)

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.Group hiding (Bool ; Unit)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

private
  variable
    ℓ : Level

open AbGroupStr renaming (_+_ to _+G_)
open RingStr
open IsRing

_==_ : ℕ → ℕ → Bool
x == y = Dec→Bool (discreteℕ x y)

∸Cancel : ∀ n → n ∸ n ≡ 0
∸Cancel zero = refl
∸Cancel (suc n) = ∸Cancel n

isFiniteSubsetℕ : ℙ ℕ → Type₀
isFiniteSubsetℕ X = ∃[ n ∈ ℕ ] ({x : ℕ} → x ∈ X → x < n)

FinSubsetℕ : Type₁
FinSubsetℕ = Σ[ X ∈ ℙ ℕ ] isFiniteSubsetℕ X

∅ : FinSubsetℕ
∅ = (λ _ → ⊥ , λ ()) , ∣ 0 , (λ ()) ∣

_∪ℙ_ : ℙ ℕ → ℙ ℕ → ℙ ℕ
X ∪ℙ Y = λ i → ∥ (i ∈ X) ⊎ (i ∈ Y) ∥ , squash

asdf : {m n : ℕ} (k : ℕ) → m < n → m < n +ℕ k
asdf {m} {n} k (x , Hx) = x +ℕ k , sym (+-assoc x k (suc m))
                                 ∙ cong (λ y → x +ℕ y) (+-comm k (suc m))
                                 ∙ +-assoc x (suc m) k
                                 ∙ cong (λ x → x +ℕ k) Hx

asdf2 : {m n : ℕ} (k : ℕ) → m < n → m < k +ℕ n
asdf2 {m} {n} k h = subst (λ x → m < x) (+-comm n k) (asdf k h)

_∪_ : FinSubsetℕ → FinSubsetℕ → FinSubsetℕ
(X , HX) ∪ (Y , HY) = (X ∪ℙ Y) , map2 (λ x y → (fst x +ℕ fst y) , foo x y) HX HY
  where
  foo : (x : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ X → x < n))
        (y : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ Y → x < n))
      → {z : ℕ} → z ∈ (X ∪ℙ Y) → z < fst x +ℕ fst y
  foo (x , Hx) (y , Hy) = ∥-rec m≤n-isProp helper
    where
    helper : {z : ℕ} → (z ∈ X) ⊎ (z ∈ Y) → z < x +ℕ y
    helper (inl h) = asdf y (Hx h)
    helper (inr h) = asdf2 x (Hy h)

infix 5 _∉_

_∉_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∉ A = ¬ x ∈ A

∉∪ : (x : ℕ) (X Y : FinSubsetℕ) → x ∉ fst (X ∪ Y) → (x ∉ fst X) × (x ∉ fst Y)
∉∪ x X Y H = (λ HX → H ∣ inl HX ∣) , (λ HY → H ∣ inr HY ∣)

module GradedAbGroup (G : ℕ → AbGroup ℓ)
                     (1G : G 0 .fst)
                     (_·G_ : {m n : ℕ} → G m .fst → G n .fst → G (m +ℕ n) .fst)
                     (·G-rid : {m : ℕ} (x : G m .fst) → x ·G 1G ≡ subst (λ y → G y .fst) (sym (+-zero m)) x)
                     (·G-lid : (x : G 0 .fst) → 1G ·G x ≡ x)
                     (·G-l0g : {m n : ℕ} (x : G m .fst) → x ·G 0g (G n .snd) ≡ 0g (G (m +ℕ n) .snd))
                     where

  ⊕G : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  ⊕G = Σ[ f ∈ ((i : ℕ) → G i .fst) ]
          ∃[ I ∈ FinSubsetℕ ] ({j : ℕ} → (j ∉ I .fst) → f j ≡ 0g (G j .snd))

  isSet⊕G : isSet ⊕G
  isSet⊕G = isSetΣ (isSetΠ (λ i → is-set (G i .snd))) λ _ → isProp→isSet squash

  0⊕G : ⊕G
  0⊕G = (λ i → 0g (G i .snd)) , ∣ ∅ , (λ _ → refl) ∣

  _+⊕G_ : ⊕G → ⊕G → ⊕G
  (f , Hf) +⊕G (g , Hg) = (λ i → G i .snd ._+G_ (f i) (g i)) , map2 (λ X Y → (fst X ∪ fst Y) , λ {j} H →
    let hf : f j ≡ 0g (G j .snd)
        hf  = snd X (∉∪ j (fst X) (fst Y) H .fst)
        hg : g j ≡ 0g (G j .snd)
        hg  = snd Y (∉∪ j (fst X) (fst Y) H .snd)
    in (λ i → G j .snd ._+G_ (hf i) (hg i)) ∙ (rid (G j .snd) _)) Hf Hg

  +⊕G-rid : (x : ⊕G) → x +⊕G 0⊕G ≡ x
  +⊕G-rid (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → rid (G i .snd) _))

  +⊕G-comm : (x y : ⊕G) → x +⊕G y ≡ y +⊕G x
  +⊕G-comm (x , _) (y , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → comm (G i .snd) _ _))

  +⊕G-assoc : (x y z : ⊕G) → x +⊕G (y +⊕G z) ≡ (x +⊕G y) +⊕G z
  +⊕G-assoc (x , _) (y , _) (z , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → assoc (G i .snd) _ _ _))

  -⊕G_ : ⊕G → ⊕G
  -⊕G (f , Hf) = (λ i → G i .snd .-_ (f i))
               , map (λ X → X .fst , λ {j} H → cong (λ z → G j .snd .-_ z) (X .snd H)
                                             ∙ GroupTheory.inv1g (AbGroup→Group (G j))) Hf

  +-⊕G : (x : ⊕G) → (x +⊕G (-⊕G x)) ≡ 0⊕G
  +-⊕G (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → invr (G i .snd) _))

  ⊕G-AbGroup : AbGroup (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  fst ⊕G-AbGroup = ⊕G
  0g (snd ⊕G-AbGroup) = 0⊕G
  _+G_ (snd ⊕G-AbGroup) = _+⊕G_
  - snd ⊕G-AbGroup = -⊕G_
  isAbGroup (snd ⊕G-AbGroup) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm

  1⊕G' : (i : ℕ) → G i .fst
  1⊕G' 0 = 1G
  1⊕G' i = 0g (G i .snd)

  1⊕G : ⊕G
  1⊕G = (1⊕G' , ∣ X , hX ∣)
     where

     X : FinSubsetℕ
     X = X' , hX'
       where
       X' : ℙ ℕ
       X' 0 = Unit , isPropUnit
       X' _ = ⊥ , isProp⊥

       hX' : isFiniteSubsetℕ X'
       hX' = ∣ 1 , foo ∣
         where
         foo : {x : ℕ} → x ∈ X' → x < 1
         foo {zero} hx = 0 , refl

     hX : {j : ℕ} → j ∉ X .fst → 1⊕G' j ≡ 0g (G j .snd)
     hX {zero} j∉X = ⊥-elim (j∉X tt)
     hX {suc j} j∉X = refl

  abstract
    helper : {n : ℕ} → (i : Fin (suc n)) → suc (toℕ i) +ℕ (suc n ∸ suc (toℕ i)) ≡ suc n
    helper {n} i = +-comm (suc (toℕ i)) _ ∙ ≤-∸-+-cancel (toℕ<n i)

  _·⊕G_ : ⊕G → ⊕G → ⊕G
  (x , Hx) ·⊕G (y , Hy) = p , q
    where
    p : (n : ℕ) → G n .fst
    p 0 = x 0 ·G y 0
    p (suc n) = ∑ (λ (i : Fin (suc n)) → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G y (suc n ∸ suc (toℕ i))))
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G (suc n)))) renaming (bigOp to ∑)

    postulate
      q : ∃[ I ∈ FinSubsetℕ ] ({j : ℕ} → j ∉ I .fst → p j ≡ 0g (G j .snd))

  apa : {m n : ℕ} → (p : m ≡ n) (x : (i : ℕ) → G i .fst) → subst (λ x → G x .fst) p (x m) ≡ x n
  apa p x = J (λ y q → subst (λ x → G x .fst) q (x _) ≡ x _) (transportRefl _) p

  ·⊕G-rid : (x : ⊕G) → x ·⊕G 1⊕G ≡ x
  ·⊕G-rid (x , h) = Σ≡Prop (λ _ → squash) (funExt (λ i → help i))
    where
    help : (n : ℕ) → ((x , h) ·⊕G 1⊕G) .fst n ≡ x n
    help 0 = ·G-rid (x 0) ∙ transportRefl _
    help (suc n) = goal
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G (suc n)))) renaming (bigOp to ∑)

      helper2 : (∑ ((λ i → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i)))) ∘ weakenFin)) ≡ 0g (G (suc n) .snd)
      helper2 =
        ∑ ((λ i → subst (λ i₁ → G i₁ .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i)))) ∘ weakenFin)
         ≡⟨ bigOpExt helper3 ⟩
        ∑ (λ (i : Fin n) → 0g (G (suc n) .snd)) ≡⟨ bigOpε n ⟩
        0g (G (suc n) .snd) ∎
        where
        test : {n : ℕ} (i : Fin n) → 1⊕G' (suc n ∸ suc (toℕ (weakenFin i))) ≡ 0g (G (suc n ∸ suc (toℕ (weakenFin i))) .snd)
        test zero = refl
        test {suc n} (suc i) = test {n} i

        helper3 : (i : Fin n) → subst (λ x → G x .fst) (helper (weakenFin i)) (x (suc (toℕ (weakenFin i))) ·G 1⊕G' (suc n ∸ suc (toℕ (weakenFin i)))) ≡
                                0g (G (suc n) .snd)
        helper3 i =
         subst (λ x → G x .fst) (helper (weakenFin i)) (x (suc (toℕ (weakenFin i))) ·G 1⊕G' (suc n ∸ suc (toℕ (weakenFin i))))
         ≡⟨ (λ j → subst (λ x → G x .fst) (helper (weakenFin i)) (x (suc (toℕ (weakenFin i))) ·G test i j)) ⟩
         subst (λ x → G x .fst) (helper (weakenFin i)) (x (suc (toℕ (weakenFin i))) ·G 0g (G (suc n ∸ suc (toℕ (weakenFin i))) .snd))
         ≡⟨ (λ j → subst (λ x → G x .fst) (helper (weakenFin i)) (·G-l0g (x (suc (toℕ (weakenFin i)))) j)) ⟩
         subst (λ x → G x .fst) (helper (weakenFin i)) (0g (G (suc (toℕ (weakenFin i)) +ℕ (suc n ∸ suc (toℕ (weakenFin i)))) .snd))
         ≡⟨ apa (helper (weakenFin i)) (λ j → 0g (G j .snd)) ⟩
            0g (G (suc n) .snd) ∎

      froop : (m n : ℕ) → (h : m ≡ 0) → x n ·G 1⊕G' m ≡ x (n +ℕ m)
      froop zero n h = ·G-rid (x n) ∙ apa (sym (+-zero n)) x
      froop (suc m) n h = ⊥-rec (snotz h)

      bepa : (n : ℕ) → x (suc (toℕ (fromℕ n))) ·G 1⊕G' (suc n ∸ suc (toℕ (fromℕ n))) ≡ x (suc (toℕ (fromℕ n) +ℕ (suc n ∸ suc (toℕ (fromℕ n)))))
      bepa n = froop (suc n ∸ suc (toℕ (fromℕ n))) (suc (toℕ (fromℕ n))) (cong (n ∸_) (toFromId n) ∙ ∸Cancel n)

      goal : (∑ λ (i : Fin (suc n)) → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i)))) ≡ x (suc n)
      goal = (∑ λ (i : Fin (suc n)) → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i))))
        ≡⟨ bigOpLast (λ i → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i)))) ⟩
             G (suc n) .snd ._+G_ (∑ ((λ i → subst (λ i → G i .fst) (helper i) (x (suc (toℕ i)) ·G 1⊕G' (suc n ∸ suc (toℕ i)))) ∘ weakenFin))
                                  (subst (λ i → G i .fst) (helper (fromℕ n)) (x (suc (toℕ (fromℕ n))) ·G 1⊕G' (suc n ∸ suc (toℕ (fromℕ n)))))
        ≡⟨ (λ i → G (suc n) .snd ._+G_ (helper2 i) (subst (λ i → G i .fst) (helper (fromℕ n)) (x (suc (toℕ (fromℕ n))) ·G 1⊕G' (suc n ∸ suc (toℕ (fromℕ n)))))) ⟩
             G (suc n) .snd ._+G_ (0g (G (suc n) .snd))
                                  (subst (λ i → G i .fst) (helper (fromℕ n)) (x (suc (toℕ (fromℕ n))) ·G 1⊕G' (suc n ∸ suc (toℕ (fromℕ n)))))
        ≡⟨ lid (G (suc n) .snd) _ ⟩
             subst (λ i → G i .fst) (helper (fromℕ n)) (x (suc (toℕ (fromℕ n))) ·G 1⊕G' (suc n ∸ suc (toℕ (fromℕ n))))
        ≡⟨ (λ i → subst (λ i → G i .fst) (helper (fromℕ n)) (bepa n i)) ⟩
             subst (λ i → G i .fst) (helper (fromℕ n)) (x (suc (toℕ (fromℕ n) +ℕ (suc n ∸ suc (toℕ (fromℕ n))))))
        ≡⟨ apa (helper (fromℕ n)) x ⟩
             x (suc n)  ∎




  ·⊕G-lid : (x : ⊕G) → 1⊕G ·⊕G x ≡ x
  ·⊕G-lid (x , h) = Σ≡Prop (λ _ → squash) (funExt (λ i → help i))
    where
    help : (i : ℕ) → (1⊕G ·⊕G (x , h)) .fst i ≡ x i
    help 0 = ·G-lid (x 0)
    help (suc i) = {!!}

  R : Ring (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  fst R = ⊕G
  0r (snd R) = 0⊕G
  1r (snd R) = 1⊕G
  _+_ (snd R) = _+⊕G_
  _·_ (snd R) = _·⊕G_
  - snd R = -⊕G_
  +IsAbGroup (isRing (snd R)) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm
  ·IsMonoid (isRing (snd R)) = makeIsMonoid isSet⊕G {!!} ·⊕G-rid ·⊕G-lid
  fst (dist (isRing (snd R)) x y z) = {!!}
  snd (dist (isRing (snd R)) x y z) = {!!}
