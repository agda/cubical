module Cubical.Data.IterativeSets.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Smallness
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.W.W
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Fibration
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Displayed.Base
open import Cubical.HITs.Replacement

open import Cubical.Data.IterativeMultisets.Base renaming (index to index-∞ ; elements to elements-V∞ ; toFib to toFib-∞)

private
  variable
    ℓ : Level

isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-∞ A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

isPropIsIterativeSet : (x : V∞ {ℓ}) → isProp (isIterativeSet x)
isPropIsIterativeSet (sup-∞ A f) = isProp× isPropIsEmbedding helper
  where
    helper : isProp ((a : A) → isIterativeSet (f a))
    helper g h i x = isPropIsIterativeSet (f x) (g x) (h x) i

V⁰ : Type (ℓ-suc ℓ)
V⁰ = Σ[ x ∈ V∞ ] isIterativeSet x

private
  variable
    x y z : V⁰ {ℓ}

-- accessing the components

index : V⁰ {ℓ} → Type ℓ
index = index-∞ ∘ fst

elements-∞ : (x : V⁰ {ℓ}) → index x → V∞ {ℓ}
elements-∞ = elements-V∞ ∘ fst

elements : (x : V⁰ {ℓ}) → index x → V⁰ {ℓ}
elements (sup-∞ _ f , _) a .fst = f a
elements (sup-∞ _ _ , isitset) a .snd = isitset .snd a

isEmbedding-elements-∞ : (x : V⁰ {ℓ}) → isEmbedding (elements-∞ x)
isEmbedding-elements-∞ (sup-∞ _ _ , its) = its .fst

isEmbedding-elements : (x : V⁰ {ℓ}) → isEmbedding (elements x)
isEmbedding-elements (sup-∞ _ _ , isitset) = isEmbeddingSndΣProp isPropIsIterativeSet _ (isitset .fst)

Embedding-elements : (x : V⁰ {ℓ}) → index x ↪ V⁰ {ℓ}
Embedding-elements x .fst = elements x
Embedding-elements x .snd = isEmbedding-elements x

V⁰↪V∞ : V⁰ {ℓ} ↪ V∞ {ℓ}
V⁰↪V∞ = EmbeddingΣProp isPropIsIterativeSet

≡V⁰-≃-≡V∞ : (x ≡ y) ≃ (x .fst ≡ y .fst)
≡V⁰-≃-≡V∞ .fst = cong fst
≡V⁰-≃-≡V∞ .snd = V⁰↪V∞ .snd _ _

_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (elements y) (x)

∈⁰-irrefl : ¬ x ∈⁰ x
∈⁰-irrefl {x = sup-∞ A f , _} (a , p) = ∈∞-irrefl {x = sup-∞ A f} (a , cong fst p)

Iso-V⁰-Emb : Iso (V⁰ {ℓ}) (Embedding (V⁰ {ℓ}) ℓ)
Iso-V⁰-Emb {ℓ} = compIso isom Σ-assoc-Iso
  where
    isom : Iso (V⁰ {ℓ}) (Σ[ F ∈ Fibration (V⁰ {ℓ}) ℓ ] isEmbedding (F .snd))
    isom .Iso.fun (sup-∞ A f , its) .fst .fst = index (sup-∞ A f , its)
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .fst = f a
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .snd = its .snd a
    isom .Iso.fun (sup-∞ A f , its) .snd = isEmbeddingSndΣProp isPropIsIterativeSet _ (its .fst)
    isom .Iso.inv E .fst = sup-∞ (E .fst .fst) (compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .fst)
    isom .Iso.inv E .snd .fst = compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .snd
    isom .Iso.inv E .snd .snd a = E .fst .snd a .snd
    isom .Iso.sec E = Σ≡Prop (λ _ → isPropIsEmbedding) refl
    isom .Iso.ret (sup-∞ _ _ , _) = Σ≡Prop isPropIsIterativeSet refl

toEmb : V⁰ {ℓ} → Embedding (V⁰ {ℓ}) ℓ
toEmb = Iso-V⁰-Emb .Iso.fun

fromEmb : Embedding (V⁰ {ℓ}) ℓ → V⁰ {ℓ}
fromEmb = Iso-V⁰-Emb .Iso.inv

-- TODO: figure out why this one computes poorly
secEmb : section (toEmb {ℓ}) (fromEmb {ℓ})
secEmb = Iso-V⁰-Emb .Iso.sec

retEmb : retract (toEmb {ℓ}) (fromEmb {ℓ})
retEmb = Iso-V⁰-Emb .Iso.ret

V⁰≃Emb : V⁰ {ℓ} ≃ Embedding (V⁰ {ℓ}) ℓ
V⁰≃Emb = isoToEquiv Iso-V⁰-Emb

Emb≃V⁰ : Embedding (V⁰ {ℓ}) ℓ ≃ V⁰ {ℓ}
Emb≃V⁰ = isoToEquiv (invIso Iso-V⁰-Emb)

isSetV⁰ : isSet (V⁰ {ℓ})
isSetV⁰ = isOfHLevelRespectEquiv 2 Emb≃V⁰ isSetEmbedding

_≃V⁰_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰ y = ((z : V⁰) → (z ∈⁰ x) → (z ∈⁰ y)) ×
          ((z : V⁰) → (z ∈⁰ y) → (z ∈⁰ x))

≃V⁰-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰ y) ≃ (x ≡ y)
≃V⁰-≃-≡V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (EmbeddingIP (toEmb x) (toEmb y)) (invEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y))

≡V⁰-≃-≃V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰ y)
≡V⁰-≃-≃V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y) (invEquiv (EmbeddingIP (toEmb x) (toEmb y)))

V⁰↪Fib : (V⁰ {ℓ}) ↪ Fibration (V⁰ {ℓ}) ℓ
V⁰↪Fib {ℓ} = compEmbedding Emb↪Fib (Iso→Embedding Iso-V⁰-Emb)
  where
    open EmbeddingIdentityPrinciple
    Emb↪Fib : Embedding (V⁰ {ℓ}) ℓ ↪ Fibration (V⁰ {ℓ}) ℓ
    Emb↪Fib .fst = toFibr
    Emb↪Fib .snd = isEmbeddingToFibr

toFib : (V⁰ {ℓ}) → Fibration (V⁰ {ℓ}) ℓ
toFib = V⁰↪Fib .fst

_≃V⁰'_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰' y = (z : V⁰) → ((z ∈⁰ x) ≃ (z ∈⁰ y))

≃V⁰'-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰' y) ≃ (x ≡ y)
≃V⁰'-≃-≡V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (FibrationIP (toFib x) (toFib y)) (invEquiv (cong toFib , V⁰↪Fib .snd x y))

≡V⁰-≃-≃V⁰' : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰' y)
≡V⁰-≃-≃V⁰' {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (cong toFib , V⁰↪Fib .snd x y) (invEquiv (FibrationIP (toFib x) (toFib y)))

isProp∈∞ : {z : V∞ {ℓ}} → isProp (z ∈∞ (x .fst))
isProp∈∞ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-elements-∞ x) z

isProp∈⁰ : {x z : V⁰ {ℓ}} → isProp (z ∈⁰ x)
isProp∈⁰ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-elements x) z

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = index

fromEmb' : (x : V⁰ {ℓ}) → (El⁰ x ↪ V⁰ {ℓ})
fromEmb' (sup-∞ A f , its) = toEmb (sup-∞ A f , its) .snd

isSetEl⁰ : (x : V⁰ {ℓ}) → isSet (El⁰ x)
isSetEl⁰ {ℓ} x = Embedding-into-isSet→isSet {A = El⁰ {ℓ} x} {B = V⁰ {ℓ}} (fromEmb' x) (isSetV⁰ {ℓ})

isProp-∈⁰-Equiv : (x y : V⁰ {ℓ}) → isProp ((z : V⁰) → (z ∈⁰ x) ≃ (z ∈⁰ y))
isProp-∈⁰-Equiv x y = isPropΠ λ z → isOfHLevel≃ 1 (isProp∈⁰ {x = x} {z = z}) (isProp∈⁰ {x = y} {z = z})

∈⁰≃∈∞ : {x z : V⁰ {ℓ}} → (z ∈⁰ x) ≃ (z .fst ∈∞ x .fst)
∈⁰≃∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz} = propBiimpl→Equiv
      (isProp∈⁰ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz})
      (isProp∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ})
      f g
    where
        f : (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx) → sup-∞ z γ ∈∞ sup-∞ x α
        f (a , p) .fst = a
        f (a , p) .snd = cong fst p
        g : sup-∞ z γ ∈∞ sup-∞ x α → (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx)
        g (a , p) .fst = a
        g (a , p) .snd = Σ≡Prop isPropIsIterativeSet p

-- Some results about smallness of iterative sets
isSmallEl⁰ : ∀ {ℓ} (x : V⁰ {ℓ}) → is[ ℓ ]Small (El⁰ x)
isSmallEl⁰ x = isℓSmallℓ (El⁰ x)

isLocallySmallV∞ : {ℓ : Level} → isLocally[ ℓ ]Small (V∞ {ℓ})
isLocallySmallV∞ {ℓ} = WInd2 (Type ℓ) (λ A → A) (Type ℓ) (λ A → A) (λ x y → is[ ℓ ]Small (x ≡ y)) step
  where
    step : {A : Type ℓ} {α : A → V∞ {ℓ}} {B : Type ℓ} {β : B → V∞ {ℓ}}
      → ((a : A) (b : B) → is[ ℓ ]Small (α a ≡ β b))
      → is[ ℓ ]Small (sup-∞ A α ≡ sup-∞ B β)
    step {A} {α} {B} {β} IH =
      isSmall-≃-isSmall
        (isSmallΣ (isℓSmallℓ (A ≃ B))
          (λ e → isSmall-≃-isSmall
            (isSmallΠ (isℓSmallℓ A) (λ a → IH a (e .fst a)))
            funExtEquiv))
        (invEquiv ≡V∞-≃-≡Equiv)

isLocallySmallV : {ℓ : Level} → isLocally[ ℓ ]Small (V⁰ {ℓ})
isLocallySmallV {ℓ} x y =
  isSmall-≃-isSmall (isLocallySmallV∞ (x .fst) (y .fst)) (invEquiv ≡V⁰-≃-≡V∞)

V⁰UARel : UARel (V⁰ {ℓ}) ℓ
V⁰UARel = locallySmall→UARel isLocallySmallV

replacementV⁰ : ∀ {ℓ} {A : Type ℓ} → (A → V⁰ {ℓ}) → V⁰ {ℓ}
replacementV⁰ α = fromEmb (Replacement V⁰UARel α , unrepEmbedding V⁰UARel α)
