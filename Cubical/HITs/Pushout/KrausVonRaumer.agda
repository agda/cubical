{-

An induction principle for paths in a pushout, described in
Kraus and von Raumer, "Path Spaces of Higher Inductive Types in Homotopy Type Theory"
https://arxiv.org/abs/1901.06022

-}

{-# OPTIONS --safe #-}
module Cubical.HITs.Pushout.KrausVonRaumer where

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.HITs.Pushout.Base as ⊔
open import Cubical.HITs.Pushout.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

private
  interpolate : {x y z : A} (q : y ≡ z)
    → PathP (λ i → x ≡ q i → x ≡ z) (_∙ q) (idfun _)
  interpolate q i p j =
    hcomp
      (λ k → λ
        { (j = i0) → p i0
        ; (j = i1) → q (i ∨ k)
        ; (i = i1) → p j
        })
      (p j)

  interpolateCompPath : {x y : A} (p : x ≡ y) {z : A} (q : y ≡ z)
   → (λ i → interpolate q i (λ j → compPath-filler p q i j)) ≡ refl
  interpolateCompPath p =
    J (λ z q → (λ i → interpolate q i (λ j → compPath-filler p q i j)) ≡ refl)
      (homotopySymInv (λ p i j → compPath-filler p refl (~ i) j) p)

module ElimL
  {f : A → B} {g : A → C} {b₀ : B}
  (P : ∀ b → Path (Pushout f g) (inl b₀) (inl b) → Type ℓ''')
  (Q : ∀ c → Path (Pushout f g) (inl b₀) (inr c) → Type ℓ''')
  (r : P b₀ refl)
  (e : (a : A) (q : inl b₀ ≡ inl (f a)) → P (f a) q ≃ Q (g a) (q ∙ push a))
  where

  Codes : (d : Pushout f g) (q : inl b₀ ≡ d) → Type ℓ'''
  Codes (inl b) q = P b q
  Codes (inr c) q = Q c q
  Codes (push a i) q =
    Glue
      (Q (g a) (interpolate (push a) i q))
      (λ
        { (i = i0) → _ , e a q
        ; (i = i1) → _ , idEquiv (Q (g a) q)
        })

  elimL : ∀ b q → P b q
  elimL _ = J Codes r

  elimR : ∀ c q → Q c q
  elimR _ = J Codes r

  refl-β : elimL b₀ refl ≡ r
  refl-β = transportRefl _

  push-β : (a : A) (q : inl b₀ ≡ inl (f a))
    → elimR (g a) (q ∙ push a) ≡ e a q .fst (elimL (f a) q)
  push-β a q =
    J-∙ Codes r q (push a)
    ∙ fromPathP
      (subst
       (λ α → PathP (λ i → Q (g a) (α i)) (e a q .fst (elimL (f a) q)) (e a q .fst (elimL (f a) q)))
       (interpolateCompPath q (push a) ⁻¹)
       refl)

module ElimR
  {f : A → B} {g : A → C} {c₀ : C}
  (P : ∀ b → Path (Pushout f g) (inr c₀) (inl b) → Type ℓ''')
  (Q : ∀ c → Path (Pushout f g) (inr c₀) (inr c) → Type ℓ''')
  (r : Q c₀ refl)
  (e : (a : A) (q : inr c₀ ≡ inl (f a)) → P (f a) q ≃ Q (g a) (q ∙ push a))
  where

  Codes : (d : Pushout f g) (q : inr c₀ ≡ d) → Type ℓ'''
  Codes (inl b) q = P b q
  Codes (inr c) q = Q c q
  Codes (push a i) q =
    Glue
      (Q (g a) (interpolate (push a) i q))
      (λ
        { (i = i0) → _ , e a q
        ; (i = i1) → _ , idEquiv (Q (g a) q)
        })

  elimL : ∀ b q → P b q
  elimL _ = J Codes r

  elimR : ∀ c q → Q c q
  elimR _ = J Codes r

  refl-β : elimR c₀ refl ≡ r
  refl-β = transportRefl _

  push-β : (a : A) (q : inr c₀ ≡ inl (f a))
    → elimR (g a) (q ∙ push a) ≡ e a q .fst (elimL (f a) q)
  push-β a q =
    J-∙ Codes r q (push a)
    ∙ fromPathP
      (subst
       (λ α → PathP (λ i → Q (g a) (α i)) (e a q .fst (elimL (f a) q)) (e a q .fst (elimL (f a) q)))
       (interpolateCompPath q (push a) ⁻¹)
       refl)

-- Example application: pushouts preserve embeddings

isEmbeddingInr :
  (f : A → B) (g : A → C)
  → isEmbedding f → isEmbedding (⊔.inr {f = f} {g = g})
isEmbeddingInr f g fEmb c₀ c₁ =
  isoToIsEquiv (iso _ (fst ∘ bwd c₁) (snd ∘ bwd c₁) bwdCong)
  where
  Q : ∀ c → ⊔.inr c₀ ≡ ⊔.inr c → Type _
  Q _ q = fiber (cong ⊔.inr) q

  P : ∀ b → ⊔.inr c₀ ≡ ⊔.inl b → Type _
  P b p = Σ[ u ∈ fiber f b ] Q _ (p ∙ cong ⊔.inl (u .snd ⁻¹) ∙ push (u .fst))

  module Bwd = ElimR P Q
    (refl , refl)
    (λ a p →
      subst
        (P (f a) p  ≃_)
        (cong (λ w → fiber (cong ⊔.inr) (p ∙ w)) (lUnit (push a) ⁻¹))
        (Σ-contractFst (inhProp→isContr (a , refl) (isEmbedding→hasPropFibers fEmb (f a)))))

  bwd : ∀ c → (t : ⊔.inr c₀ ≡ ⊔.inr c) → fiber (cong ⊔.inr) t
  bwd = Bwd.elimR

  bwdCong : ∀ {c} → (r : c₀ ≡ c) → bwd c (cong ⊔.inr r) .fst ≡ r
  bwdCong = J (λ c r → bwd c (cong ⊔.inr r) .fst ≡ r) (cong fst Bwd.refl-β)


-- Further Application: Pushouts of emedding-spans of n-Types are n-Types, for n≥0
module _ (f : A → B) (g : A → C) where
  inlrJointlySurjective :
    (z : Pushout f g) → ∥ Σ[ x ∈ (B ⊎ C) ] (⊎.rec inl inr x) ≡ z ∥
  inlrJointlySurjective =
    elimProp _
             (λ _ → isPropPropTrunc)
             (λ b → ∣ ⊎.inl b , refl ∣)
             (λ c → ∣ ⊎.inr c , refl ∣)

  preserveHLevelEmbedding :
    {n : HLevel}
    → isEmbedding f
    → isEmbedding g
    → isOfHLevel (2 + n) B
    → isOfHLevel (2 + n) C
    → isOfHLevel (2 + n) (Pushout f g)
  preserveHLevelEmbedding {n = n} fEmb gEmb isOfHLB isOfHLC =
    isOfHLevelΩ→isOfHLevel n ΩHLevelPushout
    where isEmbInr = isEmbeddingInr f g fEmb
          isEmbInrSwitched = isEmbeddingInr g f gEmb

          equivΩC :  {x : Pushout f g} (c : C) (p : inr c ≡ x)
                    → (c ≡ c) ≃ (x ≡ x)
          equivΩC c p = compEquiv (_ , isEmbInr c c) (conjugatePathEquiv p)

          equivΩB :  {x : Pushout f g} (b : B) (p : inl b ≡ x)
                    → (b ≡ b) ≃ (x ≡ x)
          equivΩB b p = compEquiv
                          (compEquiv (_ , isEmbInrSwitched b b)
                                     (congEquiv pushoutSwitchEquiv))
                          (conjugatePathEquiv p)

          ΩHLevelPushout : (x : Pushout f g) → isOfHLevel (suc n) (x ≡ x)
          ΩHLevelPushout x =
            Trunc.elim
              (λ _ → isPropIsOfHLevel {A = (x ≡ x)} (suc n))
              (λ {(⊎.inl b , p) →
                    isOfHLevelRespectEquiv
                      (suc n)
                      (equivΩB b p)
                      (isOfHLB b b);
                  (⊎.inr c , p) →
                    isOfHLevelRespectEquiv
                      (suc n)
                      (equivΩC c p)
                      (isOfHLC c c)})
              (inlrJointlySurjective x)
