{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.UnorderedPair.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level

-- TODO: (possibly) rename and move
private
    module _ where
        ≢-move-i0→i : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b)
                       (i : I) → ¬ (x ≡ y) → ¬ (p i ≡ q i)
        ≢-move-i0→i p q i x≢y pi≡qi = x≢y ((λ j → p (i ∧ j)) ∙∙ pi≡qi ∙∙ λ j → q (i ∧ ~ j))

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

unorderedPair⁰≡unorderedPair⁰ : {x y a b : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {a≢b : ¬ (a ≡ b)}
                                → ((unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ a b a≢b)
                                    ≃ (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))))
unorderedPair⁰≡unorderedPair⁰ {x = x} {y = y} {a = a} {b = b} {x≢y = x≢y} {a≢b = a≢b}
                                              = propBiimpl→Equiv (isSetV⁰ _ _) isPropRHS f g
    where
       isPropRHS : isProp (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a)))
       isPropRHS = isProp⊎ (isProp× (isSetV⁰ _ _) (isSetV⁰ _ _))
                           (isProp× (isSetV⁰ _ _) (isSetV⁰ _ _))
                           (λ (x≡a , _) (_ , y≡a) → x≢y (x≡a ∙ (sym y≡a)))

       destruct : (unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _)
                    → ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b))
       destruct p .fst = unorderedPair⁰-is-unordered-pair-sym .fst
                                    (≡V⁰-≃-≃V⁰ .fst p .fst x (lift false , refl))
       destruct p .snd = unorderedPair⁰-is-unordered-pair-sym .fst
                                    (≡V⁰-≃-≃V⁰ .fst p .fst y (lift true , refl))

       filter : ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b))
                  → ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))
       filter (inl x≡a , inl y≡a) = ⊥-elim (x≢y (x≡a ∙ (sym y≡a)))
       filter (inl x≡a , inr y≡b) = inl (x≡a , y≡b)
       filter (inr x≡b , inl y≡a) = inr (x≡b , y≡a)
       filter (inr x≡b , inr y≡b) = ⊥-elim (x≢y (x≡b ∙ (sym y≡b)))

       f : unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _
             → ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))
       f = filter ∘ destruct

       -- TODO: make more efficient somehow
       g : ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a)) → unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _
       g (inl (x≡a , y≡b)) = unorderedPair⁰-≢-witness-agnostic x≢y _
                               ∙∙ (λ i → unorderedPair⁰ (x≡a i) (y≡b i) (≢-move-i0→i x≡a y≡b i x≢y))
                               ∙∙ unorderedPair⁰-≢-witness-agnostic _ a≢b
       g (inr (x≡b , y≡a)) = (unorderedPair⁰-≢-witness-agnostic x≢y _
                               ∙∙ (λ i → unorderedPair⁰ (x≡b i) (y≡a i) (≢-move-i0→i x≡b y≡a i x≢y))
                               ∙∙ unorderedPair⁰-≢-witness-agnostic _ (λ b≡a → a≢b (sym b≡a)))
                             ∙ unorderedUnorderedPair⁰
