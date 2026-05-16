module Cubical.Data.IterativeSets.UnorderedPair.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level

unorderedPair⁰ : (x y : V⁰ {ℓ}) → ¬ (x ≡ y) → V⁰ {ℓ}
unorderedPair⁰ {ℓ} x y x≢y = fromEmb emb
    where
        emb : Embedding (V⁰ {ℓ}) ℓ
        emb .fst = Bool* {ℓ}
        emb .snd .fst (lift false) = x
        emb .snd .fst (lift true) = y
        emb .snd .snd = injEmbedding isSetV⁰ inj
            where
                inj : {a b : _} → emb .snd .fst a ≡ emb .snd .fst b → a ≡ b
                inj {lift false} {lift true} x≡y = ⊥-elim (x≢y x≡y)
                inj {lift true} {lift false} y≡x = ⊥-elim (x≢y (sym y≡x))
                inj {lift false} {lift false} _ = refl
                inj {lift true} {lift true} _ = refl

-- {x , y} ≡ {y , x}
unorderedUnorderedPair⁰ : {x y : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {y≢x : ¬ (y ≡ x)}
                            → unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ y x y≢x
unorderedUnorderedPair⁰ {x = x} {y = y} = invEq ≡V⁰-≃-≃V⁰ (f , g)
    where
        f : (z : V⁰) → z ∈⁰ unorderedPair⁰ x y _ → z ∈⁰ unorderedPair⁰ y x _
        f _ (lift false , _) .fst = lift true
        f _ (lift false , prf) .snd = prf
        f _ (lift true , _) .fst = lift false
        f _ (lift true , prf) .snd = prf

        g : (z : V⁰) → z ∈⁰ unorderedPair⁰ y x _ → z ∈⁰ unorderedPair⁰ x y _
        g _ (lift false , _) .fst = lift true
        g _ (lift false , prf) .snd = prf
        g _ (lift true , _) .fst = lift false
        g _ (lift true , prf) .snd = prf

unorderedPair⁰-is-unordered-pair : {x y z : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)}
                                    → ((z ∈⁰ (unorderedPair⁰ x y x≢y)) ≃ ((x ≡ z) ⊎ (y ≡ z)))
unorderedPair⁰-is-unordered-pair {x = x} {y = y} {z = z} = isoToEquiv isom
    where
        isom : Iso (z ∈⁰ unorderedPair⁰ x y _) ((x ≡ z) ⊎ (y ≡ z))
        isom .Iso.fun (lift false , q) = inl q
        isom .Iso.fun (lift true , q) = inr q
        isom .Iso.inv (inl _) .fst = lift false
        isom .Iso.inv (inl q) .snd = q
        isom .Iso.inv (inr _) .fst = lift true
        isom .Iso.inv (inr q) .snd = q
        isom .Iso.sec (inl _) = refl
        isom .Iso.sec (inr _) = refl
        isom .Iso.ret (lift false , _) = refl
        isom .Iso.ret (lift true , _) = refl

unorderedPair⁰-is-unordered-pair-sym : {x y z : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)}
                                         → ((z ∈⁰ (unorderedPair⁰ x y x≢y)) ≃ ((z ≡ x) ⊎ (z ≡ y)))
unorderedPair⁰-is-unordered-pair-sym {x = x} {y = y} {z = z} = isoToEquiv isom
    where
        isom : Iso (z ∈⁰ unorderedPair⁰ x y _) ((z ≡ x) ⊎ (z ≡ y))
        isom .Iso.fun (lift false , q) = inl (sym q)
        isom .Iso.fun (lift true , q) = inr (sym q)
        isom .Iso.inv (inl _) .fst = lift false
        isom .Iso.inv (inl q) .snd = sym q
        isom .Iso.inv (inr _) .fst = lift true
        isom .Iso.inv (inr q) .snd = sym q
        isom .Iso.sec (inl _) = refl
        isom .Iso.sec (inr _) = refl
        isom .Iso.ret (lift false , _) = refl
        isom .Iso.ret (lift true , _) = refl

unorderedPair⁰-≢-witness-agnostic : {x y : V⁰ {ℓ}} (x≢y₁ x≢y₂ : ¬ (x ≡ y))
                                      → unorderedPair⁰ x y x≢y₁ ≡ unorderedPair⁰ x y x≢y₂
unorderedPair⁰-≢-witness-agnostic {x = x} {y = y} x≢y₁ x≢y₂ = cong (unorderedPair⁰ x y) x≢y₁≡x≢y₂
    where
        x≢y₁≡x≢y₂ : x≢y₁ ≡ x≢y₂
        x≢y₁≡x≢y₂ = isProp→ (λ ()) x≢y₁ x≢y₂

private
  -- maybe switch a and x, as well as b and y to make it closer to the place where we use it later
  module _ {A : Type ℓ} (a b x y : A) (a≢b : ¬ a ≡ b) where
    ⊎-×-≡-distr : Iso (((a ≡ x) ⊎ (a ≡ y))
                        × ((b ≡ x) ⊎ (b ≡ y)))
                      (((a ≡ x) × (b ≡ y))
                        ⊎ ((a ≡ y) × (b ≡ x)))
    ⊎-×-≡-distr .Iso.fun (inl a≡x , inl b≡x) = ⊥-elim (a≢b (a≡x ∙ sym b≡x))
    ⊎-×-≡-distr .Iso.fun (inl a≡x , inr b≡y) = inl (a≡x , b≡y)
    ⊎-×-≡-distr .Iso.fun (inr a≡y , inl b≡x) = inr (a≡y , b≡x)
    ⊎-×-≡-distr .Iso.fun (inr a≡y , inr b≡y) = ⊥-elim (a≢b (a≡y ∙ sym b≡y))

    ⊎-×-≡-distr .Iso.inv (inl (a≡x , b≡y)) .fst = inl a≡x
    ⊎-×-≡-distr .Iso.inv (inl (a≡x , b≡y)) .snd = inr b≡y
    ⊎-×-≡-distr .Iso.inv (inr (a≡y , b≡x)) .fst = inr a≡y
    ⊎-×-≡-distr .Iso.inv (inr (a≡y , b≡x)) .snd = inl b≡x

    ⊎-×-≡-distr .Iso.sec (inl _) = refl
    ⊎-×-≡-distr .Iso.sec (inr _) = refl

    ⊎-×-≡-distr .Iso.ret (inl a≡x , inl b≡x) = ⊥-elim {A = λ _ → ⊎-×-≡-distr .Iso.inv (⊎-×-≡-distr .Iso.fun (inl a≡x , inl b≡x)) ≡ (inl a≡x , inl b≡x)} (a≢b (a≡x ∙ sym b≡x))
    ⊎-×-≡-distr .Iso.ret (inl x , inr x₁) = refl
    ⊎-×-≡-distr .Iso.ret (inr x , inl x₁) = refl
    ⊎-×-≡-distr .Iso.ret (inr a≡y , inr b≡y) = ⊥-elim {A = λ _ → Iso.inv ⊎-×-≡-distr (Iso.fun ⊎-×-≡-distr (inr a≡y , inr b≡y))
      ≡ (inr a≡y , inr b≡y)} (a≢b (a≡y ∙ sym b≡y))

unorderedPair⁰≡unorderedPair⁰ : {x y a b : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {a≢b : ¬ (a ≡ b)}
                                → ((unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ a b a≢b)
                                    ≃ (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))))
unorderedPair⁰≡unorderedPair⁰ {x = x} {y = y} {a = a} {b = b} {x≢y = x≢y} {a≢b = a≢b}
                                              = compEquiv (compEquiv ≡V⁰-≃-≃V⁰' (compEquiv L M)) (isoToEquiv (⊎-×-≡-distr x y a b x≢y))
  where
    L : ((z : V⁰) → (z ∈⁰ unorderedPair⁰ x y x≢y) ≃ (z ∈⁰ unorderedPair⁰ a b a≢b))
          ≃
        ((z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b)))
    L = equivΠCod (λ z → equivComp unorderedPair⁰-is-unordered-pair-sym
                                    unorderedPair⁰-is-unordered-pair-sym)

    M : ((z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b)))
           ≃
         ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b))
    M = propBiimpl→Equiv propLHS propRHS f g
      where
        propLHS : isProp ((z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b)))
        propLHS = isPropΠ (λ z → isOfHLevel≃ 1
                    (isProp⊎ (isSetV⁰ z x) (isSetV⁰ z y) (λ z≡x z≡y → x≢y (sym z≡x ∙ z≡y)))
                    (isProp⊎ (isSetV⁰ z a) (isSetV⁰ z b) (λ z≡a z≡b → a≢b (sym z≡a ∙ z≡b))))

        propRHS : isProp (((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b)))
        propRHS = isProp× (isProp⊎ (isSetV⁰ x a) (isSetV⁰ x b) (λ x≡a x≡b → a≢b (sym x≡a ∙ x≡b)))
                          (isProp⊎ (isSetV⁰ y a) (isSetV⁰ y b) (λ y≡a y≡b → a≢b (sym y≡a ∙ y≡b)))

        f : ((z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b))) →
             ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b))
        f E .fst = E x .fst (inl refl)
        f E .snd = E y .fst (inr refl)

        g : ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b)) →
             (z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b))
        g (inl x≡a , inl y≡a) = ⊥-elim (x≢y (x≡a ∙ sym y≡a))
        g (inl x≡a , inr y≡b) z = pathToEquiv (λ i → (z ≡ x≡a i) ⊎ (z ≡ y≡b i))
        g (inr x≡b , inl y≡a) z = compEquiv (pathToEquiv (λ i → (z ≡ x≡b i) ⊎ (z ≡ y≡a i))) ⊎-swap-≃
        g (inr x≡b , inr y≡b) = ⊥-elim (x≢y (x≡b ∙ sym y≡b))

unorderedPair⁰≡unorderedPair⁰' : {x y a b : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {a≢b : ¬ (a ≡ b)}
                                → ¬ x ≡ b
                                → (unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ a b a≢b)
                                  ≃
                                  ((x ≡ a) × (y ≡ b))
unorderedPair⁰≡unorderedPair⁰' {x = x} {y = y} {a = a} {b = b} x≢b = compEquiv unorderedPair⁰≡unorderedPair⁰
                                                                    (compEquiv (⊎-equiv (idEquiv ((x ≡ a) × (y ≡ b)))
                                                                                        (uninhabEquiv⊥ (λ p → x≢b (p .fst))))
                                                                               ⊎-IdR-⊥-≃)
