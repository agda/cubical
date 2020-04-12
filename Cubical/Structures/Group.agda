{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.InftyMagma hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)


private
  variable
    ℓ ℓ' : Level

group-axioms : (X : Type ℓ) → ∞-magma-structure X → Type ℓ
group-axioms G (_·_) = i × ii × iii
  where
  i  = isSet G
  ii = (x y z : G) → (x · (y · z)) ≡ ((x · y) · z)
  iii = Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x)) ×
                   ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e))                   

group-structure : Type ℓ → Type ℓ
group-structure = add-to-structure (∞-magma-structure) group-axioms

Groups : Type (ℓ-suc ℓ)
Groups {ℓ} = TypeWithStr ℓ group-structure

-- Extracting components of a group
⟨_⟩ : Groups {ℓ} → Type ℓ
⟨ G , _ ⟩ = G

group-operation : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-operation (_ , f , _) = f

module group-operation-syntax where

  group-operation-syntax : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  group-operation-syntax = group-operation
  infixl 20 group-operation-syntax
  syntax group-operation-syntax G x y = x ·⟨ G ⟩ y

open group-operation-syntax

group-is-set : (G : Groups {ℓ}) → isSet ⟨ G ⟩
group-is-set (_ , _ , P , _) = P

group-assoc : (G : Groups {ℓ})
            → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
group-assoc (_ , _ , _ , P , _) = P

-- Defining identity

id : (G : Groups {ℓ}) → ⟨ G ⟩
id (_ , _ , _ , _ , P) = fst P

group-rid : (G : Groups {ℓ})
          → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (id G) ≡ x
group-rid (_ , _ , _ , _ , P) x = fst ((fst (snd P)) x)

group-lid : (G : Groups {ℓ})
          → (x : ⟨ G ⟩) → (id G) ·⟨ G ⟩ x ≡ x
group-lid (_ , _ , _ , _ , P) x = snd ((fst (snd P)) x)

-- Defining the inverse function
inv : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩
inv (_ , _ , _ , _ , P) x = fst ((snd (snd P)) x)

group-rinv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (inv G x) ≡ id G
group-rinv (_ , _ , _ , _ , P) x = fst (snd ((snd (snd P)) x))

group-linv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → (inv G x) ·⟨ G ⟩ x ≡ id G
group-linv (_ , _ , _ , _ , P) x = snd (snd ((snd (snd P)) x))

-- Additive notation for groups
module additive-notation (G : Groups {ℓ}) where

  ₀ : ⟨ G ⟩
  ₀ = id G

  _+_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _+_ = group-operation G

  -_ : ⟨ G ⟩ → ⟨ G ⟩
  -_ = inv G

--Multiplicative notation for groups
module multiplicative-notation (G : Groups {ℓ}) where

  ₁ : ⟨ G ⟩
  ₁ = id G

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _·_ = group-operation G

  _⁻¹ : ⟨ G ⟩ → ⟨ G ⟩
  _⁻¹ = inv G

  ·-is-assoc = group-assoc G

  ·₁  = group-rid G

  ₁·  = group-lid G

  ·⁻¹ = group-rinv G

  ⁻¹· = group-linv G

-- Iso for groups are those for monoids
group-iso : StrIso group-structure ℓ
group-iso = add-to-iso ∞-magma-structure ∞-magma-iso group-axioms

-- Group axioms isProp

group-axioms-isProp : (X : Type ℓ)
                    → (s : ∞-magma-structure X)
                    → isProp (group-axioms X s)
group-axioms-isProp X s t = η t
  where
  𝒢 : Groups
  𝒢 = X , s , t

  is-identity : X → Type _
  is-identity e = (x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)

  α : (e : X) → isProp (is-identity e)
  α e = isPropPi (λ _ → isPropΣ (group-is-set 𝒢 _ _) (λ _ → group-is-set 𝒢 _ _))

  β : (e : X) → is-identity e → isProp ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e))
  β e is-identity-e =
   isPropPi λ { x (x' , _ , P) (x'' , Q , _) → ΣProp≡ (λ _ → isPropΣ (group-is-set 𝒢 _ _) λ _ → group-is-set 𝒢 _ _)
                                                      (inv-lemma ℳ x x' x'' P Q) }
   where
    ℳ : Monoids
    ℳ = ⟨ 𝒢 ⟩ , (e , group-operation 𝒢) ,
        group-is-set 𝒢 ,
        group-assoc 𝒢 ,
        (λ x → fst (is-identity-e x)) ,
        (λ x → snd (is-identity-e x))
                                                      

  γ : isProp (Σ[ e ∈ X ] ((x : X) → (x ·⟨ 𝒢 ⟩ e ≡ x) × (e ·⟨ 𝒢 ⟩ x ≡ x)) ×
                         ((x : X) → Σ[ x' ∈ X ] (x ·⟨ 𝒢 ⟩ x' ≡ e) × (x' ·⟨ 𝒢 ⟩ x ≡ e)))
  γ (e , P , _) (e' , Q , _) = ΣProp≡ (λ e → isPropΣ (α e) λ is-identity-e → β e is-identity-e)
                                      (e          ≡⟨ sym (fst (Q e)) ⟩
                                      e ·⟨ 𝒢 ⟩ e' ≡⟨ snd (P e') ⟩
                                      e' ∎)

  η : isProp (group-axioms X s)
  η = isPropΣ isPropIsSet
      λ _ → isPropΣ (isPropPi (λ x → isPropPi (λ y → isPropPi (λ z → group-is-set 𝒢 _ _))))
      λ _ → γ

-- Group paths equivalent to equality
group-is-SNS : SNS {ℓ} group-structure group-iso
group-is-SNS = add-axioms-SNS ∞-magma-structure ∞-magma-iso
               group-axioms group-axioms-isProp ∞-magma-is-SNS

GroupPath : (M N : Groups {ℓ}) → (M ≃[ group-iso ] N) ≃ (M ≡ N)
GroupPath M N = SIP group-structure group-iso group-is-SNS M N

-- TODO: SEPARATE TE FOLLOWING TO DIFFERENT FILES
---------------------------------------------------------------------
-- Groups basic properties 
---------------------------------------------------------------------

-- We will use the multiplicative notation for groups

module _ (G : Groups {ℓ}) where

  open multiplicative-notation G

  id-is-unique : isContr (Σ[ x ∈ ⟨ G ⟩ ] ∀ (y : ⟨ G ⟩) → (x ·⟨ G ⟩ y ≡ y) × (y ·⟨ G ⟩ x ≡ y))
  id-is-unique = (₁ , λ y → ₁· y , ·₁ y) ,
                 λ { (e , is-unit) → ΣProp≡ (λ x → isPropPi λ y → isPropΣ (group-is-set G _ _)
                                                                    λ _ →    group-is-set G _ _)
                                              (₁          ≡⟨ sym (snd (is-unit (id G))) ⟩
                                               ₁ ·⟨ G ⟩ e ≡⟨ ₁· e ⟩
                                               e ∎
                                              )}

  are-inverses : ∀ (x y : ⟨ G ⟩)
               → x · y ≡ ₁
               → (y ≡ x ⁻¹) × (x ≡ y ⁻¹)
  are-inverses x y eq = (y                ≡⟨ sym (₁· y) ⟩
                         ₁ · y            ≡⟨ sym (·-is-assoc _ _ _ ∙ cong (_· y) (⁻¹· _)) ⟩
                         (x ⁻¹) · (x · y) ≡⟨ cong ((x ⁻¹) ·_) eq ⟩
                         (x ⁻¹) · ₁       ≡⟨ ·₁ _ ⟩
                         x ⁻¹ ∎)
                     , (x                 ≡⟨ sym (·₁ x) ⟩
                        x · ₁             ≡⟨ cong (x ·_) (sym (·⁻¹ y)) ∙ ·-is-assoc _ _ _ ⟩
                        (x · y) · (y ⁻¹)  ≡⟨ cong (_· (y ⁻¹)) eq ⟩
                        ₁ · (y ⁻¹)        ≡⟨ ₁· _ ⟩
                        y ⁻¹ ∎)

  inv-involutive : ∀ (x : ⟨ G ⟩)
                 → (x ⁻¹) ⁻¹ ≡ x
  inv-involutive x = sym (snd (are-inverses x (x ⁻¹) (·⁻¹ x)))

  inv-distr : ∀ (x y : ⟨ G ⟩) → (x · y) ⁻¹ ≡ (y ⁻¹) · (x ⁻¹)
  inv-distr x y = sym (fst (are-inverses _ _ γ))
    where γ : (x · y) · ((y ⁻¹) · (x ⁻¹)) ≡ ₁
          γ = (x · y) · ((y ⁻¹) · (x ⁻¹)) ≡⟨ sym (cong (x ·_) (sym (·-is-assoc _ _ _)) ∙ ·-is-assoc _ _ _) ⟩
              x · ((y · (y ⁻¹)) · (x ⁻¹)) ≡⟨ cong (λ - → x · (- · (x ⁻¹))) (·⁻¹ y) ⟩
              x · (₁ · (x ⁻¹))            ≡⟨ cong (x ·_) (₁· (x ⁻¹)) ⟩
              x · (x ⁻¹)                  ≡⟨ ·⁻¹ x ⟩
              ₁ ∎

  left-cancel : ∀ (x y z : ⟨ G ⟩) → x · y ≡ x · z → y ≡ z
  left-cancel x y z eq = y                ≡⟨ sym (cong (_· y) (⁻¹· x) ∙ ₁· y) ⟩
                         ((x ⁻¹) · x) · y ≡⟨ sym (·-is-assoc _ _ _) ⟩
                         (x ⁻¹) · (x · y) ≡⟨ cong ((x ⁻¹) ·_) eq ⟩
                         (x ⁻¹) · (x · z) ≡⟨ ·-is-assoc _ _ _ ⟩
                         ((x ⁻¹) · x) · z ≡⟨ cong (_· z) (⁻¹· x) ∙ ₁· z ⟩
                         z ∎
                         
  right-cancel : ∀ (x y z : ⟨ G ⟩) → x · z ≡ y · z → x ≡ y
  right-cancel x y z eq = x                ≡⟨ sym (cong (x ·_) (·⁻¹ z) ∙ ·₁ x) ⟩
                          x · (z · (z ⁻¹)) ≡⟨ ·-is-assoc _ _ _ ⟩
                          (x · z) · (z ⁻¹) ≡⟨ cong (_· (z ⁻¹)) eq ⟩
                          (y · z) · (z ⁻¹) ≡⟨ sym (·-is-assoc _ _ _) ⟩
                          y · (z · (z ⁻¹)) ≡⟨ cong (y ·_) (·⁻¹ z) ∙ ·₁ y ⟩
                          y ∎

{-  -- Potencias


  _^+_ : ⟨ G ⟩ → ℕ → ⟨ G ⟩
  _^+_ x 0       = ₁
  _^+_ x (suc n) = x · (_^+_ x n)

  ^+-+ : ∀ (x : ⟨ G ⟩) (n m : ℕ) →  (x ^+ n) · (x ^+ m) ≡ x ^+ (n +ℕ m)
  ^+-+ x zero m    = ₁· _
  ^+-+ x (suc n) m = (x · (x ^+ n)) · (x ^+ m) ≡⟨ sym (·-is-assoc _ _ _) ⟩
                     x · ((x ^+ n) · (x ^+ m)) ≡⟨ cong (x ·_) IH ⟩
                     x · (x ^+ (n +ℕ m)) ∎
    where IH : (x ^+ n) · (x ^+ m) ≡ x ^+ (n +ℕ m)
          IH = ^+-+ x n m

  _^-_ : ⟨ G ⟩ → ℕ → ⟨ G ⟩
  x ^- m = (x ⁻¹) ^+ m

  ^--+ : ∀ (x : ⟨ G ⟩) (n m : ℕ) →  (x ^- n) · (x ^- m) ≡ x ^- (n +ℕ m)
  ^--+ x = ^+-+ (x ⁻¹)

  _^_ : ⟨ G ⟩ → ℤ → ⟨ G ⟩
  x ^ pos zero = ₁
  x ^ pos (suc n) = x · (x ^ (pos n))
  x ^ neg n = (x ⁻¹) ^+ n
  x ^ posneg i = ₁

  ^-+ : ∀ (x : ⟨ G ⟩) (n m : ℤ) →  (x ^ n) · (x ^ m) ≡ x ^ (n +ℤ m)
  ^-+ x n (pos zero) = ·₁ _
  ^-+ x n (pos (suc m)) = {!!}
  ^-+ x n (neg zero) = ·₁ _
  ^-+ x n (neg (suc m)) = {!!}
  ^-+ x n (posneg i) = ·₁ (x ^ n)
-}

