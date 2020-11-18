{-

   The flattening lemma for pushouts (Lemma 8.5.3 in the HoTT book) proved in a cubical style.

   The proof in the HoTT book (the core lying in Lemma 6.12.2, the flattening lemma for coequalizers)
    consists mostly of long strings of equalities about transport. This proof follows almost
    entirely from definitional equalities involving glue/unglue.

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Pushout.Flattening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout.Base

module FlatteningLemma {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A → B) (g : A → C)
                       {ℓ} (F : B → Type ℓ) (G : C → Type ℓ) (e : ∀ a → F (f a) ≃ G (g a)) where

  E : Pushout f g → Type ℓ
  E (inl x) = F x
  E (inr x) = G x
  E (push a i) = ua (e a) i

  Σf : Σ[ a ∈ A ] F (f a) → Σ[ b ∈ B ] F b
  Σf (a , x) = (f a , x)

  Σg : Σ[ a ∈ A ] F (f a) → Σ[ c ∈ C ] G c
  Σg (a , x) = (g a , (e a) .fst x)

  module FlattenIso where

    fwd : Pushout Σf Σg → Σ (Pushout f g) E
    fwd (inl (b , x)) = (inl b , x)
    fwd (inr (c , x)) = (inr c , x)
    fwd (push (a , x) i) = (push a i , ua-gluePt (e a) i x)

    bwd : Σ (Pushout f g) E → Pushout Σf Σg
    bwd (inl b , x) = inl (b , x)
    bwd (inr c , x) = inr (c , x)
    bwd (push a i , x) = hcomp (λ j → λ { (i = i0) → push (a , x) (~ j)
                                        ; (i = i1) → inr (g a , x) })
                               (inr (g a , ua-unglue (e a) i x))

    bwd-fwd : ∀ x → bwd (fwd x) ≡ x
    bwd-fwd (inl (b , x)) = refl
    bwd-fwd (inr (c , x)) = refl
    bwd-fwd (push (a , x) i) j =
      hcomp (λ k → λ { (i = i0) → push (a , ua-gluePt (e a) i0 x) (~ k)
                     ; (i = i1) → inr (g a , ua-gluePt (e a) i1 x)
                     ; (j = i1) → push (a , x) (i ∨ ~ k) })
            (inr (g a , ua-unglue (e a) i (ua-gluePt (e a) i x)))
      -- Note: the (j = i1) case typechecks because of the definitional equalities:
      --  ua-gluePt e i0 x ≡ x , ua-gluePt e i1 x ≡ e .fst x,
      --  ua-unglue-glue : ua-unglue e i (ua-gluePt e i x) ≡ e .fst x

    -- essentially: ua-glue e (i ∨ ~ k) ∘ ua-unglue e i
    sq : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B)
         → SquareP (λ i k → ua e i → ua e (i ∨ ~ k))
      {- i = i0 -} (λ k x → ua-gluePt e (~ k) x)
      {- i = i1 -} (λ k x → x)
      {- k = i0 -} (λ i x → ua-unglue e i x)
      {- k = i1 -} (λ i x → x)
    sq e i k x = ua-glue e (i ∨ ~ k) (λ { ((i ∨ ~ k) = i0) → x })
                                     (inS (ua-unglue e i x))
      -- Note: this typechecks because of the definitional equalities:
      --  ua-unglue e i0 x ≡ e .fst x, ua-glue e i1 _ (inS y) ≡ y, ua-unglue e i1 x ≡ x,
      --  ua-glue-unglue : ua-glue e i (λ { (i = i0) → x }) (inS (ua-unglue e i x)) ≡ x

    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    fwd-bwd (inl b , x) = refl
    fwd-bwd (inr c , x) = refl
    fwd-bwd (push a i , x) j =
      -- `fwd` (or any function) takes hcomps to comps on a constant family, so we must use a comp here
      comp (λ _ → Σ (Pushout f g) E)
           (λ k → λ { (i = i0) → push a (~ k) , ua-gluePt (e a) (~ k) x
                    ; (i = i1) → inr (g a) , x
                    ; (j = i1) → push a (i ∨ ~ k) , sq (e a) i k x })
            (inr (g a) , ua-unglue (e a) i x)

    isom : Iso (Σ (Pushout f g) E) (Pushout Σf Σg)
    isom = iso bwd fwd bwd-fwd fwd-bwd

  flatten : Σ (Pushout f g) E ≃ Pushout Σf Σg
  flatten = isoToEquiv FlattenIso.isom

open import Cubical.HITs.Sn
open import Cubical.HITs.Truncation
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.HITs.Susp
open import Cubical.Data.Nat

map→ : (n : ℕ) → PushoutSusp (S₊ (suc n)) → Path (hLevelTrunc (5 + n) (Susp (PushoutSusp (S₊ (suc n))))) ∣ north ∣ ∣ north ∣
map→ n a = cong ∣_∣ (merid a ∙ sym (merid (inl tt)))

fibMap : (n : ℕ) (b : Path (hLevelTrunc (5 + n) (Susp (PushoutSusp (S₊ (suc n))))) ∣ north ∣ ∣ north ∣) → Type₀
fibMap n b = fiber (map→ n) b

module _ (n : ℕ) where
  helper : {!((b
        : Path
          (HubAndSpoke (Susp (PushoutSusp (S₊ (suc n))))
           (suc (suc (suc (suc n)))))
          ∣ north ∣ ∣ north ∣) →
       (λ i → ∣ (merid (inl a) ∙ (λ i₁ → merid (inl tt) (~ i₁))) i ∣) ≡ b)
      ≃
      ((b
        : Path
          (HubAndSpoke (Susp (PushoutSusp (S₊ (suc n))))
           (suc (suc (suc (suc n)))))
          ∣ south ∣ ∣ north ∣) →
       (λ i → ∣ merid (inl tt) (~ i) ∣) ≡ b)!}
  helper = {!!}
  module x = FlatteningLemma {A = Unit} {B = PushoutSusp (S₊ (suc n))} {C = PushoutSusp (S₊ (suc n))} inl inr (λ a → (b : Path (hLevelTrunc (5 + n) (Susp (PushoutSusp (S₊ (suc n))))) ∣ north ∣ ∣ north ∣) → cong ∣_∣ (merid a ∙ sym (merid (inl tt))) ≡ b) (λ a → (b : Path (hLevelTrunc (5 + n) (Susp (PushoutSusp (S₊ (suc n))))) ∣ south ∣ ∣ north ∣) → cong ∣_∣ (sym (merid (inl tt))) ≡ b) (λ _ → pathToEquiv {!λ j → ?!})

no : (n : ℕ) (b : Path (hLevelTrunc (5 + n) (Susp (PushoutSusp (S₊ (suc n))))) ∣ north ∣ ∣ north ∣) → fibMap n b ≃ FlatteningLemma.E {A = Pushout (λ _ → tt) (λ _ → tt)} {B = {!!}} (λ x → cong ∣_∣ (merid x)) (λ x → cong ∣_∣ (merid x ∙ (sym (merid (inl tt))))) (λ p → p ≡ b ∙ cong ∣_∣ (merid (inl tt))) (λ p → p ≡ b) {!!} {!!}
no n b = {!FlatteningLemma.flatten {A = Pushout (λ _ → tt) (λ _ → tt)} {B = {!!}} (λ x → cong ∣_∣ (merid x)) (λ x → cong ∣_∣ (merid x ∙ (sym (merid (inl tt))))) (λ p → p ≡ b ∙ cong ∣_∣ (merid (inl tt))) (λ p → p ≡ b) ?!}

open import Cubical.Data.Bool
S' : (n : ℕ) → Type₀
S' zero = Bool
S' (suc n) = Susp (S' n)

ptS'n : (n : ℕ) → S' n
ptS'n zero = true
ptS'n (suc n) = north

data Sish (n : ℕ) : Type₀ where -- 2+ n
  c : Bool → Sish n
  path : (b : S' (suc n)) → c true ≡ c false
open import Cubical.HITs.S1
D : (n : ℕ) → (b : S' (suc n)) → (b : S' (suc n)) → S' (suc n)
D n north x = x
D n south north = north
D n south south = north
D n south (merid a i) = (merid a ∙ sym (merid (ptS'n n))) i
D n (merid a i) north = (merid a ∙ sym (merid (ptS'n n))) i
D n (merid a i) south = merid a (~ i)
D n (merid a i) (merid b j) = {!!}
-- D n north x = x
-- D n south north = north
-- D n south south = north
-- D (n) south (merid b i) = (merid b ∙ sym (merid a)) i
-- D (n) (merid a i) (c false) = path a (~ i)
-- D (n) (merid a i) (c true) = c true
-- D (n) (merid a i) (path b i₁) = compPath-filler (path b) (sym (path north)) i i₁

-- tihi : (n : ℕ) (b : S' (suc n)) → isEquiv (D n b)
-- tihi n = suspToPropElim (ptS'n n) (λ _ → isPropIsEquiv _) (idIsEquiv _)

-- data Wsim (n : ℕ) : Type₀ where
--   c' : (S' n) → Wsim n
--   path' : (S' n) → c' b ≡ c' (
