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
open import Cubical.Foundations.Univalence using (ua; univalence)
open import Cubical.Functions.Fibration

open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Nullary using (Discrete; yes; no)
open import Cubical.Structures.Axioms

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

-- If `f` is an embedding, we'd expect the fibers of `f` to be
-- propositions, like an injective function.
hasPropFibers : (A → B) → Type _
hasPropFibers f = ∀ y → isProp (fiber f y)

-- This can be relaxed to having all prop fibers over the image, see [hasPropFibersOfImage→isEmbedding]
hasPropFibersOfImage : (A → B) → Type _
hasPropFibersOfImage f = ∀ x → isProp (fiber f (f x))

-- some notation
_↪_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₁ ℓ₂)
A ↪ B = Σ[ f ∈ (A → B) ] isEmbedding f

hasPropFibersIsProp : isProp (hasPropFibers f)
hasPropFibersIsProp = isPropΠ (λ _ → isPropIsProp)

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

isEmbedding→hasPropFibers : isEmbedding f → hasPropFibers f
isEmbedding→hasPropFibers iE y xp
  = subst (λ f → isProp f) (lemma₀ (snd xp)) (isContr→isProp (lemma₁ iE (fst xp))) xp

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

hasPropFibersOfImage→isEmbedding : hasPropFibersOfImage f → isEmbedding f
hasPropFibersOfImage→isEmbedding {f = f} iP = hasPropFibers→isEmbedding pf where
  pf : hasPropFibers f
  pf y a b = subst (λ y → isProp (fiber f y)) (snd a) (iP (fst a)) a b

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
  → (a : A → B)
  → (e : isEmbedding a)
  ----------------------
  → ∀ {f g : C → A} →
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
Embedding-into-Discrete→Discrete (f , isEmbeddingF) _≟_ x y with f x ≟ f y
... | yes p = yes (invIsEq (isEmbeddingF x y) p)
... | no ¬p = no (¬p ∘ cong f)

Embedding-into-isProp→isProp : A ↪ B → isProp B → isProp A
Embedding-into-isProp→isProp (f , isEmbeddingF) isProp-B x y
  = invIsEq (isEmbeddingF x y) (isProp-B (f x) (f y))

Embedding-into-isSet→isSet : A ↪ B → isSet B → isSet A
Embedding-into-isSet→isSet (f , isEmbeddingF) isSet-B x y p q =
  p ≡⟨ sym (retIsEq isEquiv-cong-f p) ⟩
  cong-f⁻¹ (cong f p) ≡⟨ cong cong-f⁻¹ cong-f-p≡cong-f-q ⟩
  cong-f⁻¹ (cong f q) ≡⟨ retIsEq isEquiv-cong-f q ⟩
  q ∎
  where
    cong-f-p≡cong-f-q = isSet-B (f x) (f y) (cong f p) (cong f q)
    isEquiv-cong-f = isEmbeddingF x y
    cong-f⁻¹ = invIsEq isEquiv-cong-f

Embedding-into-hLevel→hLevel
  : ∀ n → A ↪ B → isOfHLevel (suc n) B → isOfHLevel (suc n) A
Embedding-into-hLevel→hLevel zero = Embedding-into-isProp→isProp
Embedding-into-hLevel→hLevel (suc n) (f , isEmbeddingF) Blvl x y
  = isOfHLevelRespectEquiv (suc n) (invEquiv equiv) subLvl
  where
  equiv : (x ≡ y) ≃ (f x ≡ f y)
  equiv .fst = cong f
  equiv .snd = isEmbeddingF x y
  subLvl : isOfHLevel (suc n) (f x ≡ f y)
  subLvl = Blvl (f x) (f y)

-- We now show that the powerset is the subtype classifier
-- i.e. ℙ X ≃ Σ[A ∈ Type ℓ] (A ↪ X)
Embedding→Subset : {X : Type ℓ} → Σ[ A ∈ Type ℓ ] (A ↪ X) → ℙ X
Embedding→Subset (_ , f , isEmbeddingF) x = fiber f x , isEmbedding→hasPropFibers isEmbeddingF x

Subset→Embedding : {X : Type ℓ} → ℙ X → Σ[ A ∈ Type ℓ ] (A ↪ X)
Subset→Embedding {X = X} A = D , fst , Ψ
 where
  D = Σ[ x ∈ X ] x ∈ A

  Ψ : isEmbedding fst
  Ψ w x = isEmbeddingFstΣProp (∈-isProp A)

Subset→Embedding→Subset : {X : Type ℓ} → section (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Subset→Embedding→Subset _ = funExt λ x → Σ≡Prop (λ _ → isPropIsProp) (ua (FiberIso.fiberEquiv _ x))

Embedding→Subset→Embedding : {X : Type ℓ} → retract (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Embedding→Subset→Embedding {ℓ = ℓ} {X = X} (A , f , ψ) = cong (equivFun Σ-assoc-≃) p
 where
  𝒜 = Subset→Embedding (Embedding→Subset (A , f , ψ)) .fst
  𝒻 = Subset→Embedding (Embedding→Subset (A , f , ψ)) .snd .fst
  χ = Subset→Embedding (Embedding→Subset (A , f , ψ)) .snd .snd

  p : ((𝒜 , 𝒻) , χ) ≡ ((A , f) , ψ)
  p = Σ≡Prop (λ _ → isEmbeddingIsProp) (secEq (fibrationEquiv X ℓ) (A , f))

Subset≃Embedding : {X : Type ℓ} → ℙ X ≃ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≃Embedding = isoToEquiv (iso Subset→Embedding Embedding→Subset
                                    Embedding→Subset→Embedding Subset→Embedding→Subset)

Subset≡Embedding : {X : Type ℓ} → ℙ X ≡ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≡Embedding = ua Subset≃Embedding

isEmbedding→embedsFibersIntoSingl
  : isEmbedding f
  → ∀ z → fiber f z ↪ singl z
isEmbedding→embedsFibersIntoSingl {f = f} isE z = e , isEmbE where
  e : fiber f z → singl z
  e x = f (fst x) , sym (snd x)

  isEmbE : isEmbedding e
  isEmbE u v = goal where
    -- we adjust ΣeqCf by trivial equivalences that hold judgementally, which saves compositions
    Dom′ : ∀ u v → Type _
    Dom′ u v = Σ[ p ∈ (fst u ≡ fst v) ] PathP (λ i → f (p i) ≡ z) (snd u) (snd v)
    Cod′ : ∀ u v → Type _
    Cod′ u v = Σ[ p ∈ (f (fst u) ≡ f (fst v)) ] PathP (λ i → p i ≡ z) (snd u) (snd v)
    ΣeqCf : Dom′ u v ≃ Cod′ u v
    ΣeqCf = Σ-cong-equiv-fst (_ , isE _ _)

    dom→ : u ≡ v → Dom′ u v
    dom→ p = cong fst p , cong snd p
    dom← : Dom′ u v → u ≡ v
    dom← p i = p .fst i , p .snd i

    cod→ : e u ≡ e v → Cod′ u v
    cod→ p = cong fst p , cong (sym ∘ snd) p
    cod← : Cod′ u v → e u ≡ e v
    cod← p i = p .fst i , sym (p .snd i)

    goal : isEquiv _
    goal .equiv-proof x .fst .fst =
      dom← (equivCtr ΣeqCf (cod→ x) .fst)
    goal .equiv-proof x .fst .snd j =
      cod← (equivCtr ΣeqCf (cod→ x) .snd j)
    goal .equiv-proof x .snd (g , p) i .fst =
      dom← (equivCtrPath ΣeqCf (cod→ x) (dom→ g , cong cod→ p) i .fst)
    goal .equiv-proof x .snd (g , p) i .snd j =
      cod← (equivCtrPath ΣeqCf (cod→ x) (dom→ g , cong cod→ p) i .snd j)

isEmbedding→hasPropFibers′ : isEmbedding f → hasPropFibers f
isEmbedding→hasPropFibers′ {f = f} iE z =
  Embedding-into-isProp→isProp (isEmbedding→embedsFibersIntoSingl iE z) (isContr→isProp (isContrSingl _))

embedIsProp : {f : A → B}
            → isEmbedding f
            → isProp B
            → isProp A
embedIsProp isEmb isPropB a b = equivFun (invEquiv (_ , isEmb a b)) (isPropB _ _)

universeEmbedding :
  ∀ {ℓ ℓ₁ : Level}
  → (F : Type ℓ → Type ℓ₁)
  → (∀ X → F X ≃ X)
  → isEmbedding F
universeEmbedding F liftingEquiv = hasPropFibersOfImage→isEmbedding propFibersF where
  lemma : ∀ A B → (F A ≡ F B) ≃ (B ≡ A)
  lemma A B = (F A ≡ F B)  ≃⟨ univalence ⟩
              (F A ≃ F B) ≃⟨ equivComp (liftingEquiv A) (liftingEquiv B) ⟩
              (A ≃ B)     ≃⟨ invEquivEquiv ⟩
              (B ≃ A)     ≃⟨ invEquiv univalence ⟩
              (B ≡ A)      ■
  fiberSingl : ∀ X → fiber F (F X) ≃ singl X
  fiberSingl X = Σ-cong-equiv-snd (λ _ → lemma _ _)
  propFibersF : hasPropFibersOfImage F
  propFibersF X = embedIsProp (isEquiv→isEmbedding (fiberSingl X .snd)) (isContr→isProp (isContrSingl X))

liftEmbedding : (ℓ ℓ₁ : Level)
              → isEmbedding (Lift {i = ℓ} {j = ℓ₁})
liftEmbedding ℓ ℓ₁ = universeEmbedding (Lift {j = ℓ₁}) (λ _ → invEquiv LiftEquiv)

module FibrationIdentityPrinciple {B : Type ℓ} {ℓ₁} where
  -- note that fibrationEquiv (for good reason) uses ℓ₁ = ℓ-max ℓ ℓ₁, so we have to work
  -- some universe magic to achieve good universe polymorphism

  -- First, prove it for the case that's deal with in fibrationEquiv
  Fibration′ = Fibration B (ℓ-max ℓ ℓ₁)

  module Lifted (f g : Fibration′) where
    f≃g′ : Type (ℓ-max ℓ ℓ₁)
    f≃g′ = ∀ b → fiber (f .snd) b ≃ fiber (g .snd) b

    Fibration′IP : f≃g′ ≃ (f ≡ g)
    Fibration′IP =
        f≃g′
      ≃⟨ equivΠCod (λ _ → invEquiv univalence) ⟩
        (∀ b → fiber (f .snd) b ≡ fiber (g .snd) b)
      ≃⟨ funExtEquiv ⟩
        fiber (f .snd) ≡ fiber (g .snd)
      ≃⟨ invEquiv (congEquiv (fibrationEquiv B ℓ₁)) ⟩
        f ≡ g
      ■

  -- Then embed into the above case by lifting the type
  L : Type _ → Type _ -- local synonym fixing the levels of Lift
  L = Lift {i = ℓ₁} {j = ℓ}

  liftFibration : Fibration B ℓ₁ → Fibration′
  liftFibration (A , f) = L A , f ∘ lower

  hasPropFibersLiftFibration : hasPropFibers liftFibration
  hasPropFibersLiftFibration (A , f) =
    embedIsProp (isEquiv→isEmbedding (snd fiberChar))
      (isPropΣ (isEmbedding→hasPropFibers (liftEmbedding _ _) A)
               λ _ → isEquiv→hasPropFibers (snd (invEquiv (preCompEquiv LiftEquiv))) _)
    where
    fiberChar : fiber liftFibration (A , f)
              ≃ (Σ[ (E , eq) ∈ fiber L A ] fiber (_∘ lower) (transport⁻ (λ i → eq i → B) f))
    fiberChar =
        fiber liftFibration (A , f)
      ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPath≃PathΣ) ⟩
        (Σ[ (E , g) ∈ Fibration B ℓ₁ ] Σ[ eq ∈ (L E ≡ A) ] PathP (λ i → eq i → B) (g ∘ lower) f)
      ≃⟨ boringSwap ⟩
        (Σ[ (E , eq) ∈ fiber L A ] Σ[ g ∈ (E → B) ] PathP (λ i → eq i → B) (g ∘ lower) f)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-snd λ _ → transportEquiv (PathP≡Path⁻ _ _ _)) ⟩
        (Σ[ (E , eq) ∈ fiber L A ] fiber (_∘ lower) (transport⁻ (λ i → eq i → B) f))
      ■ where
      boringSwap : _
      boringSwap = isoToEquiv (iso (λ ((E , g) , (eq , p)) → ((E , eq) , (g , p)))
                                   (λ ((E , g) , (eq , p)) → ((E , eq) , (g , p))) (λ _ → refl) (λ _ → refl))

  isEmbeddingLiftFibration : isEmbedding liftFibration
  isEmbeddingLiftFibration = hasPropFibers→isEmbedding hasPropFibersLiftFibration

  -- and finish off
  module _ (f g : Fibration B ℓ₁) where
    open Lifted (liftFibration f) (liftFibration g)
    f≃g : Type (ℓ-max ℓ ℓ₁)
    f≃g = ∀ b → fiber (f .snd) b ≃ fiber (g .snd) b

    FibrationIP : f≃g ≃ (f ≡ g)
    FibrationIP =
      f≃g  ≃⟨ equivΠCod (λ b → equivComp (Σ-cong-equiv-fst LiftEquiv)
                                          (Σ-cong-equiv-fst LiftEquiv)) ⟩
      f≃g′ ≃⟨ Fibration′IP ⟩
      (liftFibration f ≡ liftFibration g) ≃⟨ invEquiv (_ , isEmbeddingLiftFibration _ _) ⟩
      (f ≡ g) ■
open FibrationIdentityPrinciple renaming (f≃g to _≃Fib_) using (FibrationIP) public

Embedding : (B : Type ℓ₁) → (ℓ : Level) → Type (ℓ-max ℓ₁ (ℓ-suc ℓ))
Embedding B ℓ = Σ[ A ∈ Type ℓ ] A ↪ B

module EmbeddingIdentityPrinciple {B : Type ℓ} {ℓ₁} (f g : Embedding B ℓ₁) where
  module _ where
    open Σ f renaming (fst to F) public
    open Σ g renaming (fst to G) public
    open Σ (f .snd) renaming (fst to ffun; snd to isEmbF) public
    open Σ (g .snd) renaming (fst to gfun; snd to isEmbG) public
  f≃g : Type _
  f≃g = (∀ b → fiber ffun b → fiber gfun b) ×
         (∀ b → fiber gfun b → fiber ffun b)
  toFibr : Embedding B ℓ₁ → Fibration B ℓ₁
  toFibr (A , (f , _)) = (A , f)

  isEmbeddingToFibr : isEmbedding toFibr
  isEmbeddingToFibr w x = fullEquiv .snd where
    -- carefully managed such that (cong toFibr) is the equivalence
    fullEquiv : (w ≡ x) ≃ (toFibr w ≡ toFibr x)
    fullEquiv = compEquiv (congEquiv (invEquiv Σ-assoc-≃)) (invEquiv (Σ≡PropEquiv (λ _ → isEmbeddingIsProp)))

  EmbeddingIP : f≃g ≃ (f ≡ g)
  EmbeddingIP =
      f≃g
    ≃⟨ isoToEquiv (invIso toProdIso) ⟩
      (∀ b → (fiber ffun b → fiber gfun b) × (fiber gfun b → fiber ffun b))
    ≃⟨ equivΠCod (λ _ → isEquivPropBiimpl→Equiv (isEmbedding→hasPropFibers isEmbF _)
                                                 (isEmbedding→hasPropFibers isEmbG _)) ⟩
      (∀ b → (fiber (f .snd .fst) b) ≃ (fiber (g .snd .fst) b))
    ≃⟨ FibrationIP (toFibr f) (toFibr g) ⟩
      (toFibr f ≡ toFibr g)
    ≃⟨ invEquiv (_ , isEmbeddingToFibr _ _) ⟩
      f ≡ g
    ■
open EmbeddingIdentityPrinciple renaming (f≃g to _≃Emb_) using (EmbeddingIP) public
