
module Cubical.Categories.Multicategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

private variable
  ℓ ℓ' ℓ'' ℓa : Level
  A : Type ℓ
  B : A → Type ℓ
  C : ∀ a → B a → Type ℓ

Σ-idl-≃ : {A : Type ℓ} → (Σ[ _ ∈ Unit* {ℓ} ] A) ≃ A
Σ-idl-≃ = strictEquiv snd (λ x → tt* , x)

Σ-idl : (A : Type ℓ) → (Σ[ _ ∈ Unit* {ℓ} ] A) ≡ A
Σ-idl A = ua Σ-idl-≃

Σ-idr-≃ : {A : Type ℓ} → (Σ[ _ ∈ A ] Unit* {ℓ}) ≃ A
Σ-idr-≃ = strictEquiv fst (λ x → x , tt*)

Σ-idr : (A : Type ℓ) → (Σ[ _ ∈ A ] Unit* {ℓ}) ≡ A
Σ-idr A = ua Σ-idr-≃

Σ-assoc : (A : Type ℓ) (B : A → Type ℓ') (C : ∀ a → B a → Type ℓ'')
        → (Σ[ a ∈ Σ A B ] C (fst a) (snd a)) ≡ (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
Σ-assoc A B C = ua Σ-assoc-≃

record ArityType ℓa : Type (ℓ-suc ℓa) where
  field
    isArity : Type ℓa → Type ℓa
    isArity-⊤ : isArity Unit*
    isArity-Σ : isArity A → (∀ a → isArity (B a)) → isArity (Σ A B)
    isArity-idl : (ha : isArity A) → PathP (λ i → isArity (Σ-idl A i)) (isArity-Σ isArity-⊤ λ _ → ha) ha
    isArity-idr : (ha : isArity A) → PathP (λ i → isArity (Σ-idr A i)) (isArity-Σ ha λ _ → isArity-⊤) ha
    isArity-assoc : (ha : isArity A) (hb : ∀ a → isArity (B a)) (hc : ∀ a b → isArity (C a b))
              → PathP (λ i → isArity (Σ-assoc A B C i)) (isArity-Σ (isArity-Σ ha hb) (uncurry hc)) (isArity-Σ ha λ a → isArity-Σ (hb a) (hc a))

  Arity : Type (ℓ-suc ℓa)
  Arity = TypeWithStr ℓa isArity

  Arity⊤ : Arity
  Arity⊤ = Unit* , isArity-⊤

  ArityΣ : (I : Arity) → (⟨ I ⟩ → Arity) → Arity
  ArityΣ I J = (Σ[ x ∈ ⟨ I ⟩ ] ⟨ J x ⟩) , isArity-Σ (str I) λ a → str (J a)

  syntax ArityΣ I (λ x → J) = ArityΣ[ x ∈ I ] J

  _Arity≃_ : Arity → Arity → Type ℓa
  I Arity≃ J = Σ[ e ∈ (⟨ I ⟩ ≃ ⟨ J ⟩) ] PathP (λ i → isArity (ua e i)) (str I) (str J)

  ArityΣ-idl : (I : Arity) → (ArityΣ[ _ ∈ Arity⊤ ] I) Arity≃ I
  ArityΣ-idl I = Σ-idl-≃ , isArity-idl (str I)

  ArityΣ-idr : (I : Arity) → (ArityΣ[ _ ∈ I ] Arity⊤) Arity≃ I
  ArityΣ-idr I = Σ-idr-≃ , isArity-idr (str I)

  ArityΣ-assoc : (I : Arity) (J : ⟨ I ⟩ → Arity) (K : ∀ a → ⟨ J a ⟩ → Arity)
             → (ArityΣ[ a ∈ ArityΣ I J ] K (fst a) (snd a)) Arity≃ (ArityΣ[ a ∈ I ] ArityΣ[ b ∈ J a ] K a b)
  ArityΣ-assoc I J K = Σ-assoc-≃ , isArity-assoc (str I) (λ a → str (J a)) (λ a b → str (K a b))

record Multicategory (S : ArityType ℓa) ℓ ℓ' : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓa)) where
  open ArityType S
  field
    ob : Type ℓ
    Hom : (I : Arity) (xs : ⟨ I ⟩ → ob) (y : ob) → Type ℓ'
    isSetHom : (I : Arity) (xs : ⟨ I ⟩ → ob) (y : ob) → isSet (Hom I xs y)

  field
    id : {x : ob} → Hom Arity⊤ (λ _ → x) x
    _⋆_ : {I : Arity} {J : ⟨ I ⟩ → Arity} {xss : ∀ a → ⟨ J a ⟩ → ob} {ys : ⟨ I ⟩ → ob} {z : ob}
        → (fs : ∀ a → Hom (J a) (xss a) (ys a)) → (g : Hom I ys z) → Hom (ArityΣ I J) (uncurry xss) z

  _∘_ : {I : Arity} {J : ⟨ I ⟩ → Arity} {xss : ∀ a → ⟨ J a ⟩ → ob} {ys : ⟨ I ⟩ → ob} {z : ob}
      → (g : Hom I ys z) → (fs : ∀ a → Hom (J a) (xss a) (ys a)) → Hom (ArityΣ I J) (uncurry xss) z
  g ∘ f = f ⋆ g

  PathA : {I J : Arity} {x : ⟨ J ⟩ → ob} {y : ob} (e : I Arity≃ J)
        → (h : Hom I (λ a → x (e .fst .fst a)) y) (h' : Hom J x y) → Type ℓ'
  PathA {x = x} {y = y} (e , p) h h' = PathP (λ i → Hom (ua e i , p i) (λ a → x (ua-unglue e i a)) y) h h'

  -- This gives an error for some reason
  -- field
  --   ⋆IdL : {I : Arity} {xs : ⟨ I ⟩ → ob} {y : ob} (f : Hom I xs y)
  --        → PathA (ArityΣ-idr I) ((λ _ → id) ⋆ f) f
    
  --   ⋆IdR : {I : Arity} {xs : ⟨ I ⟩ → ob} {y : ob} (f : Hom I xs y)
  --        → PathA (ArityΣ-idl I) ((λ _ → f) ⋆ id) f
    
  --   ⋆Assoc : {I : Arity} {J : ⟨ I ⟩ → Arity} {K : ∀ a → ⟨ J a ⟩ → Arity}
  --          → {xsss : ∀ a b → ⟨ K a b ⟩ → ob} {yss : ∀ a → ⟨ J a ⟩ → ob} {zs : ⟨ I ⟩ → ob} {w : ob}
  --          → (fss : ∀ a b → Hom (K a b) (xsss a b) (yss a b)) (gs : ∀ a → Hom (J a) (yss a) (zs a)) (h : Hom I zs w)
  --          → PathA (ArityΣ-assoc I J K) (uncurry fss ⋆ (gs ⋆ h)) ((λ a → fss a ⋆ gs a) ⋆ h)

