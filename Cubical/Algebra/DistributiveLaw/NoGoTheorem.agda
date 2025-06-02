{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.NoGoTheorem where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Empty
open import Cubical.Data.Containers.Set.Base
open import Cubical.Algebra.MndContainer.Base
open import Cubical.Algebra.DistributiveLaw.Mnd
open import Cubical.Relation.Nullary

open MndContainer
open IsMndContainer
open MndDistributiveLaw

private
  variable
    ℓs ℓp : Level

-- Helper functions for the no-go theorem

case : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → A → A → (Dec P) → A
case ifyes ifno (yes _) = ifyes
case ifyes ifno (no _) = ifno

cased : ∀ {ℓ ℓ' ℓ''} {P : Type ℓ} {A : Type ℓ'} {B : A → Type ℓ''} 
        → (a a' : A) (b : B a) (b' : B a')
        → (p : Dec P) → B (case a a' p)
cased _ _ ifyes ifno (yes _) = ifyes
cased _ _ ifyes ifno (no _) = ifno

decLem₁ : {ℓa ℓb ℓc ℓp : Level} {A : Type ℓa} {B : A → Type ℓb} {C : Type ℓc}
        {P : Type ℓp} (dec : Discrete P)
        (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂) (g : (a : A) → B a → C)
        (p p' : P)
        → case (g a₁ b₁) (g a₂ b₂) (dec p p')
        ≡ g (case a₁ a₂ (dec p p')) (cased a₁ a₂ b₁ b₂ (dec p p'))
decLem₁ dec a₁ a₂ b₁ b₂ g p p' i with dec p p' 
... | (yes _) = g a₁ b₁
... | (no _)  = g a₂ b₂

decLem₂ : {ℓa ℓb ℓc ℓp : Level} {A : Type ℓa} {B : A → Type ℓb} {C : Type ℓc}
        {P : Type ℓp} (dec : Discrete P)
        (a₁ a₂ : A) (c₁ c₂ : C)
        (p p' : P)
        → cased {B = λ a → B a → C} a₁ a₂ (const c₁) (const c₂) (dec p p')
        ≡ const (case c₁ c₂ (dec p p'))
decLem₂ dec a₁ a₂ c₁ c₂ p p' i with dec p p' 
... | (yes _) = const c₁
... | (no _)  = const c₂

decLem₃ : {ℓa ℓp : Level} {A : Type ℓa} 
        {P : Type ℓp} (dec : Discrete P)
        (a₁ a₂ a₃ : A) (p₁ p₂ p₃ : P)
        (pdist : ¬ (p₁ ≡ p₂))
        → case a₁ (case a₂ a₃ (dec p₃ p₂)) (dec p₃ p₁)
        ≡ case a₂ (case a₁ a₃ (dec p₃ p₁)) (dec p₃ p₂)
decLem₃ dec a₁ a₂ a₃ p₁ p₂ p₃ pdist with dec p₃ p₁ | dec p₃ p₂
... | (yes e) | (yes e') = rec (pdist (sym e ∙ e'))
... | (yes e) | (no e')  = refl
... | (no e)  | (yes e') = refl
... | (no e)  | (no e')  = refl

dec⊤ : {ℓ : Level} → Discrete (Unit* {ℓ})
dec⊤ tt* tt* = yes refl

decRefl : {ℓ : Level} {A : Type ℓ}
        (dec : Discrete A) (a : A)
        → Σ[ e ∈ a ≡ a ] dec a a ≡ yes e
decRefl dec a with dec a a
... | (yes e) = (e , refl)
... | (no e)  = rec (e refl) 

transpFun : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : Type ℓc}
            (a a' : A) (e : a ≡ a')
            (f : B a → C)
          → transport (λ i → B (e i) → C) f ≡ f ∘ transport (λ i → B (e (~ i)))
transpFun {B = B} a a' e f i b = transportRefl (f (transp (λ j → B (e (~ j))) i0 b)) i

--------

ConstantShape : (ℓs ℓp : Level) 
                (S : Type ℓs) (P : S → Type ℓp) 
                (s : S) → Type (ℓ-suc ℓp)
ConstantShape _ _ S P s = P s ≡ ⊥* 

record S3Property (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)}
                  (Aₘ : MndContainer (S ◁ P & setS & setP)) 
                  (s : S) (f : P s → S) : Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  field
    posInhabited : NonEmpty (P s)
    decEq : Discrete (P s)
    s3Shape : (p : P s) → σ Aₘ s (λ p' → case 
        (ι Aₘ) 
        (f p')
      (decEq p' p)) ≡ ι Aₘ
    s3Pos : (p : P s) → PathP (λ i → P (s3Shape p i) → P s)
                        (λ p' → pr₁ Aₘ _ _ p')
                        (λ p' → p)
open S3Property

compositeS3 : (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)}
              (Aₘ : MndContainer (S ◁ P & setS & setP))
              (s : S) (f : P s → S)
              (s3 : S3Property S P Aₘ s f)
              (T : Type ℓs) (Q : T → Type ℓp) {setT : isSet T} {setQ : ∀ {t} → isSet (Q t)}
              (Bₘ : MndContainer (T ◁ Q & setT & setQ))
              (distr : MndDistributiveLaw S P setS setP T Q setT setQ Aₘ Bₘ)
              (t : T) (p : P s) 
              → u₁ distr s (λ p' → case t (ι Bₘ) (decEq s3 p' p)) ≡ t
compositeS3 S P Aₘ s f s3 T Q Bₘ distr t p = step₁ ∙ step₂ ∙ step₃ ∙ step₄ ∙ step₅ ∙ unit-ιA-shape₁ distr t
  where
    step₁ : u₁ distr s (λ p' → case 
                  t
                  (ι Bₘ)
                (decEq s3 p' p)) 
          ≡ u₁ distr s (λ p' → case 
                  (u₁ distr (ι Aₘ) (λ _ → t))
                  (u₁ distr (f p') (λ _ → ι Bₘ))
                (decEq s3 p' p))
    step₁ i = u₁ distr s (λ p' → case 
                (unit-ιA-shape₁ distr t (~ i)) 
                (unit-ιB-shape₁ distr (f p') (~ i)) 
              (decEq s3 p' p))

    step₂ : u₁ distr s (λ p' → case 
                (u₁ distr (ι Aₘ) (λ _ → t))
                (u₁ distr (f p') (λ _ → ι Bₘ))
              (decEq s3 p' p))
            ≡ u₁ distr s (λ p' →
                u₁ distr (case (ι Aₘ) (f p') (decEq s3 p' p))
                         (const (case t (ι Bₘ) (decEq s3 p' p)))
              )
    step₂ i = u₁ distr s (λ p' → (decLem₁ (decEq s3) (ι Aₘ) (f p') (const t) (const (ι Bₘ)) (u₁ distr) p' p 
                                  ∙ cong (u₁ distr (case (ι Aₘ) (f p') (decEq s3 p' p))) (decLem₂ (decEq s3) _ _ _ _ p' p)
                                 ) i
                         )

    step₃ : u₁ distr s (λ p' → u₁ distr
              (case (ι Aₘ) (f p') (decEq s3 p' p))
              (const (case t (ι Bₘ) (decEq s3 p' p)))
            )
            ≡ u₁ distr 
                (σ Aₘ s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)))
                (λ p' → case t (ι Bₘ) (decEq s3 (pr₁ Aₘ _ _ p') p))
    step₃ i = mul-A-shape₁ distr s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)) (λ p₁ _ → case t (ι Bₘ) (decEq s3 p₁ p)) (~ i)

    step₄ : u₁ distr 
              (σ Aₘ s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)))
              (λ p' → case t (ι Bₘ) (decEq s3 (pr₁ Aₘ _ _ p') p))
            ≡ u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (decEq s3 p p))
    step₄ i = u₁ distr (s3Shape s3 p i) (λ p' → case t (ι Bₘ) (decEq s3 (s3Pos s3 p i p') p))

    step₅ : u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (decEq s3 p p))
        ≡ u₁ distr (ι Aₘ) (const t)
    step₅ i = u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (snd (decRefl (decEq s3) p) i))

module _ (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)}
         (Aₘ : MndContainer (S ◁ P & setS & setP))
         (s : S) (f : P s → S)
         (s3 : S3Property S P Aₘ s f)
         (T : Type ℓs) (Q : T → Type ℓp) {setT : isSet T} {setQ : ∀ {t} → isSet (Q t)}
         (Bₘ : MndContainer (T ◁ Q & setT & setQ))
         (distr : MndDistributiveLaw S P setS setP T Q setT setQ Aₘ Bₘ) where

  step₁ : (t t' : T) (constt : ConstantShape _ _ _ Q t)
          (p p' : P s)
        → σ Bₘ t (const (ι Bₘ))
        ≡ σ Bₘ (u₁ distr s (λ y → case t (ι Bₘ) (decEq s3 y p)))
               (λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y)
                               (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
               )
  step₁ t t' constt p p' i = σ Bₘ (compositeS3 S P Aₘ s f s3 T Q Bₘ distr t p (~ i)) 
                                  (toPathP {A = λ i → Q (compositeS3 S P Aₘ s f s3 T Q Bₘ distr t p (~ i)) → T} 
                                           {x = const (ι Bₘ)}
                                           {y = λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y) 
                                                         (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
                                           }
                                           (transpFun {B = Q} _ _ (sym (compositeS3 S P Aₘ s f s3 T Q Bₘ distr t p)) (const (ι Bₘ)) 
                                            ∙ funExt (λ x → rec* (transport constt (subst⁻ Q (sym (compositeS3 S P Aₘ s f s3 T Q Bₘ distr t p)) x)))
                                           )
                                           i
                                  )

  step₂ : (t t' : T) (p p' : P s)
        → σ Bₘ (u₁ distr s (λ y → case t (ι Bₘ) (decEq s3 y p)))
               (λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y)
                               (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
               )
        ≡ u₁ distr s (λ y → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p'))))
  step₂ t t' p p' = sym (mul-B-shape₁ distr _ _ _)

  step₃Aux : (t t' : T) (p p' : P s) (pdist : ¬ (p ≡ p'))
             (y : P s)
           → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p')))
           ≡ case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p)
  step₃Aux t t' p p' pdist y with decEq s3 y p | decEq s3 y p'
  ... | (yes e) | (yes e') = rec (pdist (sym e ∙ e'))
  ... | (yes e) | (no e')  = unit-r (isMndContainer Bₘ) t
  ... | (no e)  | (yes e') = unit-l (isMndContainer Bₘ) t'
  ... | (no e)  | (no e')  = unit-r (isMndContainer Bₘ) (ι Bₘ)

  step₃ : (t t' : T) (p p' : P s) (pdist : ¬ (p ≡ p'))
        → u₁ distr s (λ y → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p'))))
        ≡ u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
  step₃ t t' p p' pdist i = u₁ distr s (λ y → step₃Aux t t' p p' pdist y i)

  mainLem : (t t' : T) (constt : ConstantShape _ _ _ Q t)
            (p p' : P s) (pdist : ¬ (p ≡ p')) 
          → t ≡ u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
  mainLem t t' constt p p' pdist = sym (unit-r (isMndContainer Bₘ) t) ∙ step₁ t t' constt p p' ∙ step₂ t t' p p' ∙ step₃ t t' p p' pdist

  noGoTheorem : (t t' : T) (tdist : ¬ (t ≡ t'))
                (constt : ConstantShape _ _ _ Q t)
                (constt' : ConstantShape _ _ _ Q t')
                (p p' : P s) (pdist : ¬ (p ≡ p'))
              → ⊥
  noGoTheorem t t' tdist constt constt' p p' pdist = tdist (mainLem t t' constt p p' pdist 
                                                           ∙ aux 
                                                           ∙ sym (mainLem t' t constt' p' p (pdist ∘ sym))
                                                           )
    where
      aux : u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
          ≡ u₁ distr s (λ y → case t' (case t (ι Bₘ) (decEq s3 y p)) (decEq s3 y p'))
      aux i = u₁ distr s (λ y → decLem₃ (decEq s3) t t' (ι Bₘ) p p' y pdist i)
