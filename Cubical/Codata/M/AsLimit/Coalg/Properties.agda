{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Prod

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ ; idfun )
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv

open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Codata.M.AsLimit.Coalg.Base
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

module Cubical.Codata.M.AsLimit.Coalg.Properties where

open Iso

-- Construction of Coalgebras from M-types, defined in
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

-----------------------------------------------------------------------------
-- The limit of a Polynomial functor over a Container is a Final Coalgebra --
-----------------------------------------------------------------------------

M-coalg : ∀ {ℓ} {S : Container ℓ} → Coalg₀ S
M-coalg {S = S} = (M S) , out-fun

Final : ∀ {ℓ} {S : Container ℓ} → Type (ℓ-suc ℓ)
Final {S = S} = Σ[ X,ρ ∈ Coalg₀ S ] ∀ (C,γ : Coalg₀ S) → isContr ((C,γ) ⇒ (X,ρ))

--------------------------------------------------------
-- Properties of Bisimulations and (Final) Coalgebras --
--------------------------------------------------------

U : ∀ {ℓ} {S : Container ℓ} (C,γ : Coalg₀ S) → Type ℓ
U {S = S} (C , γ) =
  Σ[ f ∈ (C → M S) ] (out-fun ∘ f ≡ P₁ f ∘ γ)

U-is-Unit-Iso :
  ∀ {ℓ} {S : Container ℓ} (C,γ : Coalg₀ S)
  ------------------------------------
  → Iso {ℓ = ℓ} {ℓ' = ℓ} (C,γ ⇒ M-coalg) (Lift Unit)
U-is-Unit-Iso {ℓ = ℓ} {S = S} C,γ@(C , γ) =
  U C,γ
    Iso⟨ idIso ⟩
  (Σ[ f ∈ (C → M S) ] (out-fun ∘ f ≡ step f))
    Iso⟨ comp-abstr'0 ⟩
  (Σ[ f ∈ (C → M S) ] (in-fun ∘ out-fun ∘ f ≡ in-fun ∘ step f))
    Iso⟨ Σ-ap-iso₂ (λ f → pathToIso (cong (λ k → k ≡ in-fun ∘ step f) (computation-abstract'1 f))) ⟩
  (Σ[ f ∈ (C → M S) ] (f ≡ in-fun ∘ step f))
    Iso⟨ idIso ⟩
  (Σ[ f ∈ (C → M S) ] (f ≡ Ψ f))
    Iso⟨ Σ-ap-iso (lemma10-Iso C,γ) (λ _ → idIso) ⟩
  (Σ[ c ∈ Cone C,γ ] (e c ≡ Ψ (e c)))
    Iso⟨ Σ-ap-iso₂ (λ c → pathToIso λ i → e c ≡ funExt⁻ (commutivity) c i) ⟩
  (Σ[ c ∈ Cone C,γ ] (e c ≡ e (Φ c)))
    Iso⟨ Σ-ap-iso₂ (λ c → e-inj-Iso) ⟩
  (Σ[ c ∈ Cone C,γ ] (c ≡ Φ c))
    Iso⟨ idIso ⟩
  (Σ[ (u , q) ∈ Cone C,γ ] ((u , q) ≡ (ϕ₀ u , ϕ₁ u q)))
    Iso⟨ (Σ-ap-iso₂ λ {(u , q) → invIso (Σ-split-iso {x = (u , q)} {y = (ϕ₀ u , ϕ₁ u q)})}) ⟩
  (Σ[ (u , q) ∈ Cone C,γ ]
  (Σ[ p ∈ u ≡ ϕ₀ u ] (PathP (λ i → Cone₁ C,γ (p i)) q (ϕ₁ u q))))
    Iso⟨ (iso (λ {((u , p) , q , r) → (u , q) , p , r}) (λ {((u , q) , p , r) → (u , p) , (q , r)}) (λ _ → refl) λ _ → refl) ⟩
  (Σ[ (u , p) ∈ (Σ[ u ∈ Cone₀ C,γ ] (u ≡ ϕ₀ u)) ]
  (Σ[ q ∈ Cone₁ C,γ u ] (PathP (λ i → Cone₁ C,γ (p i)) q (ϕ₁ u q))))
    Iso⟨ invIso (Σ-ap-iso (missing-0-Iso) λ x → missing-2-Iso) ⟩
  (Σ[ _ ∈ Lift {ℓ-zero} {ℓ} Unit ] (Lift {ℓ-zero} {ℓ} Unit))
    Iso⟨ (iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ a i → lift tt , lift tt)) ⟩
  Lift {ℓ-zero} {ℓ} Unit ∎Iso
  where
    e = inv (lemma10-Iso C,γ)

    step : ∀ {Y : Type ℓ} (f : C → Y) → C → P₀ S Y
    step {Y = Y} f = P₁ f  ∘ γ

    Ψ : ∀ (f : C → M S) → C → M S
    Ψ f = in-fun ∘ step f

    ϕ₀ : ∀ (u : (n : ℕ) → C → Wₙ S n) → (n : ℕ) → C → Wₙ S n
    ϕ₀ u 0 = λ x → lift tt
    ϕ₀ u (suc n) = step (u n)

    ϕ₁ :
      ∀ (u : (n : ℕ) → C → Wₙ S n)
      → (g : (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n)
      → (n : ℕ) → πₙ S ∘ (ϕ₀ u (suc n)) ≡ ϕ₀ u n
    ϕ₁ u g 0 = funExt λ _ → refl {x = lift tt}
    ϕ₁ u g (suc n) = cong step (g n)

    Φ : Cone C,γ → Cone C,γ
    Φ (u , g) = ϕ₀ u , ϕ₁ u g

    computation-abstract'0 : {f g : C → P₀ S (M S)} → Iso (in-fun ∘ f ≡ in-fun ∘ g) (f ≡ g)
    computation-abstract'0 {f} {g} = iso→fun-Injection-Iso {ℓ = ℓ} {A = P₀ S (M S)} {B = M S} {C = C} (shift-iso S) {f = f} {g = g}

    abstract
      comp-abstr'0 : Iso (Σ[ f ∈ (C → M S) ] (out-fun ∘ f ≡ step f))
                         (Σ[ f ∈ (C → M S) ] (in-fun ∘ out-fun ∘ f ≡ in-fun ∘ step f))
      comp-abstr'0 = Σ-ap-iso₂ (λ f → invIso (computation-abstract'0 {f = out-fun ∘ f} {g = step f}))

      computation-abstract'1 : (f : C → M S) → in-fun {S = S} ∘ out-fun ∘ f ≡ f
      computation-abstract'1 f =
        in-fun {S = S} ∘ out-fun ∘ f
          ≡⟨ cong (λ a → a ∘ f) in-inverse-out ⟩
        f ∎

    postulate -- long proof..
      commutivity : Ψ ∘ e ≡ e ∘ Φ

    e-inj-Iso : ∀ {x y}
      → Iso (e x ≡ e y)
                 (x ≡ y)
    e-inj-Iso = iso→inv-Injection-Iso-x (lemma10-Iso C,γ)

    private
      u0 : Cone₀ C,γ
      u0 = λ { 0 _ → lift tt ; (suc n) → step (u0 n) }

      p0 : (n : ℕ) → u0 n ≡ ϕ₀ u0 n
      p0 0 = refl
      p0 (suc n) = refl

    missing-0-Iso : Iso (Lift {ℓ-zero} {ℓ} Unit) (Σ[ u ∈ (Cone₀ C,γ) ] (u ≡ ϕ₀ u))
    missing-0-Iso =
      Lift Unit
        Iso⟨ iso (λ _ _ → lift tt) (λ _ → lift tt) (λ _ → refl) (λ _ → refl) ⟩
      (C → Lift Unit)
        Iso⟨ invIso (lemma11-Iso {S = S} (λ n → C → Wₙ S n) λ n u → P₁ u ∘ γ) ⟩
      Σ[ u ∈ (Cone₀ C,γ) ] ((n : ℕ) → u (suc n) ≡ ϕ₀ u (suc n))
        Iso⟨ Σ-ap-iso₂ (λ _ → iso (λ {a 0 → refl ; a (suc n) → a n})
                                   (λ b → b ∘ suc)
                                   (λ b → funExt λ {0 → refl ; (suc n) → refl})
                                   λ _ → refl) ⟩
      Σ[ u ∈ (Cone₀ C,γ) ] ((n : ℕ) → u n ≡ ϕ₀ u n)
        Iso⟨ Σ-ap-iso₂ (λ _ → funExtIso) ⟩
      (Σ[ u ∈ (Cone₀ C,γ) ] (u ≡ ϕ₀ u)) ∎Iso

    private
      mi = fun missing-0-Iso (lift tt)

    missing-2-Iso :
      Iso
        (Lift {ℓ-zero} {ℓ} Unit)
        (Σ[ q ∈ (Cone₁ C,γ (mi .fst)) ]
          (PathP (λ i → Cone₁ C,γ (mi .snd i))
            q
            (ϕ₁ (mi .fst) q)))
    missing-2-Iso =
      Lift Unit
        Iso⟨ iso (λ _ _ _ → lift tt) (λ _ → lift tt) (λ _ _ _ _ → lift tt) (λ _ _ → lift tt) ⟩
      (πₙ S ∘ (mi .fst (suc 0)) ≡ mi .fst 0)
        Iso⟨ invIso (lemma11-Iso {S = S} (λ n → πₙ S ∘ mi .fst (suc n) ≡ mi .fst n) λ n g → cong step g) ⟩
      (Σ[ q ∈ (Cone₁ C,γ (mi .fst)) ] ((n : ℕ) → q (suc n) ≡ ϕ₁ (mi .fst) q (suc n)))
        Iso⟨ Σ-ap-iso₂ (λ x → idIso) ⟩
      (Σ[ q ∈ (Cone₁ C,γ (mi .fst)) ] ((n : ℕ) →
        PathP (λ x → πₙ S ∘ ((mi .snd x) (suc (suc n))) ≡ (mi .snd x) (suc n))
          (q (suc n))
          (ϕ₁ (mi .fst) q (suc n))))
        Iso⟨ Σ-ap-iso₂ (λ x → funExtIso) ⟩
      (Σ[ q ∈ (Cone₁ C,γ (mi .fst)) ] (
        PathP (λ x → (n : ℕ) → πₙ S ∘ ((mi .snd x) (suc (suc n))) ≡ (mi .snd x) (suc n))
          (q ∘ suc)
          (ϕ₁ (mi .fst) q ∘ suc)))
        Iso⟨ Σ-ap-iso₂ (λ x →
             iso (λ {a i 0 → refl ; a i (suc n) → a i n})
                 (λ a i n → a i (suc n))
                 (λ {_ _ _ 0 → refl ; a _ i (suc n) → a i (suc n)})
                 λ _ → refl) ⟩
      (Σ[ q ∈ (Cone₁ C,γ (mi .fst)) ] (PathP (λ i → Cone₁ C,γ (mi .snd i))
                                             q
                                             (ϕ₁ (mi .fst) q))) ∎Iso

U-contr : ∀ {ℓ} {S : Container ℓ} (C,γ : Coalg₀ S) → isContr (U C,γ)
U-contr {ℓ} C,γ = inv (contr-is-ext-Iso {A = U C,γ} (U-is-Unit-Iso C,γ)) (lift tt , λ { (lift tt) → refl })
  where
    isContrIsPropPath : ∀ {ℓ} {A : Type ℓ} → (x : isContr A) → ∀ y → isProp (x .fst ≡ y)
    isContrIsPropPath {A = A} x y = isContr→isProp (isContr→isContrPath x (x .fst) y)

    contr-is-ext-Iso-helper :
      ∀ {ℓ} {A B : Type ℓ}
      → (p : Iso A B)
      → ((a : A) → Iso (∀ y → a ≡ y) (∀ y → (fun p a) ≡ y))
    fun (contr-is-ext-Iso-helper (iso f g rightI leftI) a) x y = cong f (x (g y)) ∙ rightI y
    inv (contr-is-ext-Iso-helper (iso f g rightI leftI) a) x y = sym (leftI a) ∙ cong g (x (f y)) ∙ leftI y
    rightInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) b = funExt λ y → isContrIsPropPath (f a , b) y (cong f (sym (leftI a) ∙ cong g (b (f (g y))) ∙ leftI (g y)) ∙ rightI y) (b y)
    leftInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) b = funExt λ y → isContrIsPropPath (a , b) y (sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ rightI (f y)) ∙ leftI y) (b y)

    -- Can this be generalized to Iso A B → Iso (H A) (H B) , not just for H = isContr ?
    contr-is-ext-Iso : ∀ {ℓ} {A B : Type ℓ} → Iso A B → Iso (isContr A) (isContr B)
    contr-is-ext-Iso {A = A} {B} p = Σ-ap-iso p (contr-is-ext-Iso-helper p)

----------------------------------------------------
-- Finality properties for bisimulation relations --
----------------------------------------------------

lim-terminal : ∀ {ℓ} {S : Container ℓ} {C,γ : Coalg₀ S} → isContr (C,γ ⇒ M-coalg)
lim-terminal {C,γ = C,γ} = inv (U-is-Unit-Iso C,γ) (lift tt) , U-contr C,γ .snd

coalg-unfold : ∀ {ℓ} {S : Container ℓ} → (C,γ : Coalg₀ S) → (_⇒_ {S = S} (C,γ) (M-coalg {S = S}))
coalg-unfold C,γ = lim-terminal {C,γ = C,γ} .fst

-- unique function into final coalg
coalg-unfold-universal : ∀ {ℓ} {S : Container ℓ} → (C,γ : Coalg₀ S) → (y : C,γ ⇒ M-coalg) → fst lim-terminal ≡ y
coalg-unfold-universal C,γ = lim-terminal {C,γ = C,γ} .snd

-- unique function into final coalg
coalg-unfold-function : ∀ {ℓ} {S : Container ℓ} → (C,γ : Coalg₀ S) → (C,γ .fst) → (M-coalg .fst)
coalg-unfold-function C,γ y = (coalg-unfold C,γ) .fst y

M-final-coalg : ∀ {ℓ} {S : Container ℓ} → Final {S = S}
M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → lim-terminal {C,γ = C,γ}

-- final-is-contr : ∀ {ℓ} {S : Container {ℓ}} → isContr (Final {S = S})
-- final-is-contr = M-final-coalg , λ y → {!!}

final-coalg-property-2 : ∀ {ℓ} {S : Container ℓ} → (C : Coalg₀ S) → (F : Final {S = S}) → ∀ (f g : C ⇒ F .fst) → f ≡ g
final-coalg-property-2 C F f g = (sym (F .snd C .snd f)) ∙ (F .snd C .snd g) -- follows from contractability
