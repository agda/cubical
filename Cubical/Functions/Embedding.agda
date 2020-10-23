{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Functions.Embedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Functions.Fibration
open import Cubical.Relation.Nullary using (Discrete; yes; no)

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ
    f : A → B
    w x : A
    y z : B

-- Embeddings are generalizations of injections. The usual
-- definition of injection as:
--
--    f x ≡ f y → x ≡ y
--
-- is not well-behaved with higher h-levels, while embeddings
-- are.
isEmbedding : (A → B) → Type _
isEmbedding f = ∀ w x → isEquiv {A = w ≡ x} (cong f)

isEmbeddingIsProp : isProp (isEmbedding f)
isEmbeddingIsProp {f = f} = isPropΠ2 λ _ _ → isPropIsEquiv (cong f)

-- If A and B are h-sets, then injective functions between
-- them are embeddings.
--
-- Note: It doesn't appear to be possible to omit either of
-- the `isSet` hypotheses.
injEmbedding
  : {f : A → B}
  → isSet A → isSet B
  → (∀{w x} → f w ≡ f x → w ≡ x)
  → isEmbedding f
injEmbedding {f = f} iSA iSB inj w x
  = isoToIsEquiv (iso (cong f) inj sect retr)
  where
  sect : section (cong f) inj
  sect p = iSB (f w) (f x) _ p

  retr : retract (cong f) inj
  retr p = iSA w x _ p

private
  lemma₀ : (p : y ≡ z) → fiber f y ≡ fiber f z
  lemma₀ {f = f} p = λ i → fiber f (p i)

  lemma₁ : isEmbedding f → ∀ x → isContr (fiber f (f x))
  lemma₁ {f = f} iE x = value , path
    where
    value : fiber f (f x)
    value = (x , refl)

    path : ∀(fi : fiber f (f x)) → value ≡ fi
    path (w , p) i
      = case equiv-proof (iE w x) p of λ
      { ((q , sq) , _)
      → hfill (λ j → λ { (i = i0) → (x , refl)
                      ; (i = i1) → (w , sq j)
                      })
          (inS (q (~ i) , λ j → f (q (~ i ∨ j))))
          i1
      }

-- If `f` is an embedding, we'd expect the fibers of `f` to be
-- propositions, like an injective function.
hasPropFibers : (A → B) → Type _
hasPropFibers f = ∀ y → isProp (fiber f y)

-- some notation
_↪_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₁ ℓ₂)
A ↪ B = Σ[ f ∈ (A → B) ] hasPropFibers f


hasPropFibersIsProp : isProp (hasPropFibers f)
hasPropFibersIsProp = isPropΠ (λ _ → isPropIsProp)

isEmbedding→hasPropFibers : isEmbedding f → hasPropFibers f
isEmbedding→hasPropFibers iE y (x , p)
  = subst (λ f → isProp f) (lemma₀ p) (isContr→isProp (lemma₁ iE x)) (x , p)

private
  fibCong→PathP
    : {f : A → B}
    → (p : f w ≡ f x)
    → (fi : fiber (cong f) p)
    → PathP (λ i → fiber f (p i)) (w , refl) (x , refl)
  fibCong→PathP p (q , r) i = q i , λ j → r j i

  PathP→fibCong
    : {f : A → B}
    → (p : f w ≡ f x)
    → (pp : PathP (λ i → fiber f (p i)) (w , refl) (x , refl))
    → fiber (cong f) p
  PathP→fibCong p pp = (λ i → fst (pp i)) , (λ j i → snd (pp i) j)

PathP≡fibCong
  : {f : A → B}
  → (p : f w ≡ f x)
  → PathP (λ i → fiber f (p i)) (w , refl) (x , refl) ≡ fiber (cong f) p
PathP≡fibCong p
  = isoToPath (iso (PathP→fibCong p) (fibCong→PathP p) (λ _ → refl) (λ _ → refl))

hasPropFibers→isEmbedding : hasPropFibers f → isEmbedding f
hasPropFibers→isEmbedding {f = f} iP w x .equiv-proof p
  = subst isContr (PathP≡fibCong p) (isProp→isContrPathP (λ i → iP (p i)) fw fx)
  where
  fw : fiber f (f w)
  fw = (w , refl)

  fx : fiber f (f x)
  fx = (x , refl)

isEmbedding≡hasPropFibers : isEmbedding f ≡ hasPropFibers f
isEmbedding≡hasPropFibers
  = isoToPath
      (iso isEmbedding→hasPropFibers
           hasPropFibers→isEmbedding
           (λ _ → hasPropFibersIsProp _ _)
           (λ _ → isEmbeddingIsProp _ _))

isEquiv→hasPropFibers : isEquiv f → hasPropFibers f
isEquiv→hasPropFibers e b = isContr→isProp (equiv-proof e b)

isEquiv→isEmbedding : isEquiv f → isEmbedding f
isEquiv→isEmbedding e = λ _ _ → congEquiv (_ , e) .snd

iso→isEmbedding : ∀ {ℓ} {A B : Type ℓ}
  → (isom : Iso A B)
  -------------------------------
  → isEmbedding (Iso.fun isom)
iso→isEmbedding {A = A} {B} isom = (isEquiv→isEmbedding (equivIsEquiv (isoToEquiv isom)))

isEmbedding→Injection :
  ∀ {ℓ} {A B C : Type ℓ}
  → (a : A -> B)
  → (e : isEmbedding a)
  ----------------------
  → ∀ {f g : C -> A} ->
  ∀ x → (a (f x) ≡ a (g x)) ≡ (f x ≡ g x)
isEmbedding→Injection a e {f = f} {g} x = sym (ua (cong a , e (f x) (g x)))

-- if `f` has a retract, then `cong f` has, as well. If `B` is a set, then `cong f`
-- further has a section, making `f` an embedding.
module _ {f : A → B} (retf : hasRetract f) where
  open Σ retf renaming (fst to g ; snd to ϕ)

  congRetract : f w ≡ f x → w ≡ x
  congRetract {w = w} {x = x} p = sym (ϕ w) ∙∙ cong g p ∙∙ ϕ x

  isRetractCongRetract : retract (cong {x = w} {y = x} f) congRetract
  isRetractCongRetract p = transport (PathP≡doubleCompPathˡ _ _ _ _) (λ i j → ϕ (p j) i)

  hasRetract→hasRetractCong : hasRetract (cong {x = w} {y = x} f)
  hasRetract→hasRetractCong = congRetract , isRetractCongRetract

  retractableIntoSet→isEmbedding : isSet B → isEmbedding f
  retractableIntoSet→isEmbedding setB w x =
    isoToIsEquiv (iso (cong f) congRetract (λ _ → setB _ _ _ _) (hasRetract→hasRetractCong .snd))

Embedding-into-Discrete→Discrete : A ↪ B → Discrete B → Discrete A
Embedding-into-Discrete→Discrete (f , propFibers) _≟_ x y with f x ≟ f y
... | yes p = yes (cong fst (propFibers (f y) (x , p) (y , refl)))
... | no ¬p = no (¬p ∘ cong f)

Embedding-into-isProp→isProp : A ↪ B → isProp B → isProp A
Embedding-into-isProp→isProp (f , hasPropFibers-f) isProp-B x y
  = invIsEq (hasPropFibers→isEmbedding hasPropFibers-f x y) (isProp-B (f x) (f y))

Embedding-into-isSet→isSet : A ↪ B → isSet B → isSet A
Embedding-into-isSet→isSet (f , hasPropFibers-f) isSet-B x y p q =
  p ≡⟨ sym (retIsEq isEquiv-cong-f p) ⟩
  cong-f⁻¹ (cong f p) ≡⟨ cong cong-f⁻¹ cong-f-p≡cong-f-q ⟩
  cong-f⁻¹ (cong f q) ≡⟨ retIsEq isEquiv-cong-f q ⟩
  q ∎
  where
    cong-f-p≡cong-f-q = isSet-B (f x) (f y) (cong f p) (cong f q)
    isEquiv-cong-f = hasPropFibers→isEmbedding hasPropFibers-f x y
    cong-f⁻¹ = invIsEq isEquiv-cong-f

Embedding-into-hLevel→hLevel
  : ∀ n → A ↪ B → isOfHLevel (suc n) B → isOfHLevel (suc n) A
Embedding-into-hLevel→hLevel zero = Embedding-into-isProp→isProp
Embedding-into-hLevel→hLevel (suc n) (f , hasPropFibers-f) Blvl x y
  = isOfHLevelRespectEquiv (suc n) (invEquiv equiv) subLvl
  where
  equiv : (x ≡ y) ≃ (f x ≡ f y)
  equiv .fst = cong f
  equiv .snd = hasPropFibers→isEmbedding hasPropFibers-f x y
  subLvl : isOfHLevel (suc n) (f x ≡ f y)
  subLvl = Blvl (f x) (f y)


-- We now show that the powerset is the subtype classifier
-- i.e. ℙ X ≃ Σ[A ∈ Type ℓ] (A ↪ X)
Embedding→Subset : {X : Type ℓ} → Σ[ A ∈ Type ℓ ] (A ↪ X) → ℙ X
Embedding→Subset (_ , f , isPropFiber) x = fiber f x , isPropFiber x

Subset→Embedding : {X : Type ℓ} → ℙ X → Σ[ A ∈ Type ℓ ] (A ↪ X)
Subset→Embedding {X = X} A = D , fst , ψ
 where
  D = Σ[ x ∈ X ] x ∈ A

  ψ : hasPropFibers fst
  ψ x ((y , y∈A) , y≡x) ((z , z∈A) , z≡x) = ΣPathP (r , q)
   where
    p : y ≡ z
    p = y≡x ∙ sym z≡x

    r : (y , y∈A) ≡ (z , z∈A)
    r = Σ≡Prop (∈-isProp A) p

    q : PathP (λ i → p i ≡ x) y≡x z≡x
    q i j = hcomp (λ k → λ { (j = i1) → x
                           ; (i = i0) → y≡x j
                           ; (i = i1) → z≡x (~ k ∨ j) })
                  (y≡x (i ∨ j))


Subset→Embedding→Subset : {X : Type ℓ} → section (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Subset→Embedding→Subset _ = funExt λ x → Σ≡Prop (λ _ → isPropIsProp) (ua (FiberIso.fiberEquiv _ x))

Embedding→Subset→Embedding : {X : Type ℓ} → retract (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Embedding→Subset→Embedding {ℓ = ℓ} {X = X} (A , f , ψ) = cong (Σ-assoc-≃ .fst) p
 where
 χ = Subset→Embedding (Embedding→Subset (A , f , ψ)) .snd .snd

 p : (((Σ[ x ∈ X ] fiber f x) , fst) , χ) ≡ ((A , f) , ψ)
 p = Σ≡Prop (λ _ → hasPropFibersIsProp) (equivToIso (fibrationEquiv X ℓ) .Iso.leftInv (A , f))

Subset≃Embedding : {X : Type ℓ} → ℙ X ≃ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≃Embedding = isoToEquiv (iso Subset→Embedding Embedding→Subset
                                    Embedding→Subset→Embedding Subset→Embedding→Subset)

Subset≡Embedding : {X : Type ℓ} → ℙ X ≡ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≡Embedding = ua Subset≃Embedding
