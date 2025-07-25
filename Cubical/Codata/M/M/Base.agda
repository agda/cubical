{-# OPTIONS --guardedness #-}

-- Construction of M-types from
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

module Cubical.Codata.M.M.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Nat.Algebra

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sum

open import Cubical.Codata.M.helper
open import Cubical.Codata.M.Container
open import Cubical.Codata.M.Coalg.Base

open Iso

private
  limit-collapse : ∀ {ℓ} {S : Container ℓ} (X : ℕ → Type ℓ) (l : (n : ℕ) → X n → X (suc n)) → (x₀ : X 0) → ∀ (n : ℕ) → X n
  limit-collapse X l x₀ 0 = x₀
  limit-collapse {S = S} X l x₀ (suc n) = l n (limit-collapse {S = S} X l x₀ n)

lemma11-Iso :
  ∀ {ℓ} {S : Container ℓ} (X : ℕ → Type ℓ) (l : (n : ℕ) → X n → X (suc n))
  → Iso (Σ[ x ∈ ((n : ℕ) → X n)] ((n : ℕ) → x (suc n) ≡ l n (x n)))
         (X 0)
fun (lemma11-Iso X l) (x , y) = x 0
inv (lemma11-Iso {S = S} X l) x₀ = limit-collapse {S = S} X l x₀ , (λ n → refl {x = limit-collapse {S = S} X l x₀ (suc n)})
rightInv (lemma11-Iso X l) _ = refl
leftInv (lemma11-Iso {ℓ = ℓ} {S = S} X l) (x , y) i =
  let temp = χ-prop (x 0) (fst (inv (lemma11-Iso {S = S} X l) (fun (lemma11-Iso {S = S} X l) (x , y))) , refl , (λ n → refl {x = limit-collapse {S = S} X l (x 0) (suc n)})) (x , refl , y)
  in temp i .fst , proj₂ (temp i .snd)
  where
    open AlgebraPropositionality
    open NatSection

    X-fiber-over-ℕ : (x₀ : X 0) -> NatFiber NatAlgebraℕ ℓ
    X-fiber-over-ℕ x₀ = record { Fiber = X ; fib-zero = x₀ ; fib-suc = λ {n : ℕ} xₙ → l n xₙ }

    X-section : (x₀ : X 0) → (z : Σ[ x ∈ ((n : ℕ) → X n)] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n))) -> NatSection (X-fiber-over-ℕ x₀)
    X-section = λ x₀ z → record { section = fst z ; sec-comm-zero = proj₁ (snd z) ; sec-comm-suc = proj₂ (snd z) }

    Z-is-Section : (x₀ : X 0) →
      Iso (Σ[ x ∈ ((n : ℕ) → X n)] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
          (NatSection (X-fiber-over-ℕ x₀))
    fun (Z-is-Section x₀) (x , (z , y)) = record { section = x ; sec-comm-zero = z ; sec-comm-suc = y }
    inv (Z-is-Section x₀) x = NatSection.section x , (sec-comm-zero x , sec-comm-suc x)
    rightInv (Z-is-Section x₀) _ = refl
    leftInv (Z-is-Section x₀) (x , (z , y)) = refl

    -- S≡T
    χ-prop' : (x₀ : X 0) → isProp (NatSection (X-fiber-over-ℕ x₀))
    χ-prop' x₀ a b = SectionProp.S≡T isNatInductiveℕ (X-section x₀ (inv (Z-is-Section x₀) a)) (X-section x₀ (inv (Z-is-Section x₀) b))

    χ-prop : (x₀ : X 0) → isProp (Σ[ x ∈ ((n : ℕ) → X n) ] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
    χ-prop x₀ = subst isProp (sym (isoToPath (Z-is-Section x₀))) (χ-prop' x₀)

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

-- Shift is equivalence (12) and (13) in the proof of Theorem 7
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

-- TODO: This definition is inefficient, it should be updated to use some cubical features!
shift-iso : ∀ {ℓ} (S : Container ℓ) -> Iso (P₀ S (M S)) (M S)
shift-iso S@(A , B) =
  P₀ S (M S)
    Iso⟨ Σ-cong-iso-snd
         (λ x → iso (λ f → (λ n z → f z .fst n) , λ n i a → f a .snd n i)
                    (λ (u , q) z → (λ n → u n z) , λ n i → q n i z)
                    (λ _ → refl)
                    (λ _ → refl)) ⟩
  (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → X (sequence S) n) ] ((n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)))
    Iso⟨ invIso α-iso-step-5-Iso ⟩
  (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
        Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
           ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                               (π (sequence S) ∘ u (suc n))
                               (u n)))
    Iso⟨ α-iso-step-1-4-Iso-lem-12 ⟩
  M S ∎Iso
    where
      α-iso-step-5-Iso-helper0 :
        ∀ (a : (ℕ -> A))
        → (p : (n : ℕ) → a (suc n) ≡ a n)
        → (n : ℕ)
        → a n ≡ a 0
      α-iso-step-5-Iso-helper0 a p 0 = refl
      α-iso-step-5-Iso-helper0 a p (suc n) = p n ∙ α-iso-step-5-Iso-helper0 a p n

      α-iso-step-5-Iso-helper1-Iso :
        ∀ (a : ℕ -> A)
        → (p : (n : ℕ) → a (suc n) ≡ a n)
        → (u : (n : ℕ) → B (a n) → Wₙ S n)
        → (n : ℕ)
        → (PathP (λ x → B (p n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n)) ≡
             (πₙ S ∘ (subst (\k -> B k → Wₙ S (suc n)) (α-iso-step-5-Iso-helper0 a p (suc n))) (u (suc n))
         ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n))
      α-iso-step-5-Iso-helper1-Iso  a p u n =
        PathP (λ x → B (p n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n)
          ≡⟨ PathP≡Path (λ x → B (p n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n) ⟩
        subst (λ k → B k → Wₙ S n) (p n) (πₙ S ∘ u (suc n)) ≡ (u n)
          ≡⟨ (λ i → transp (λ j → B (α-iso-step-5-Iso-helper0 a p n (i ∧ j)) → Wₙ S n) (~ i) (subst (λ k → B k → Wₙ S n) (p n) (πₙ S ∘ u (suc n)))
                  ≡ transp (λ j → B (α-iso-step-5-Iso-helper0 a p n (i ∧ j)) → Wₙ S n) (~ i) (u n)) ⟩
        subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (subst (λ k → B k → Wₙ S n) (p n) (πₙ S ∘ u (suc n))) ≡
        subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n)
          ≡⟨ (λ i → sym (substComposite (λ k → B k → Wₙ S n) (p n) (α-iso-step-5-Iso-helper0 a p n) (πₙ S ∘ u (suc n))) i
                  ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n)) ⟩
        subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p (suc n)) (πₙ S ∘ u (suc n)) ≡
        subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n)
          ≡⟨ (λ i → substCommSlice (λ k → B k → Wₙ S (suc n)) (λ k → B k → Wₙ S n)
                                   (λ a x x₁ → (πₙ S) (x x₁))
                                   (α-iso-step-5-Iso-helper0 a p (suc n)) (u (suc n)) i
                  ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n)) ⟩
        πₙ S ∘ subst (λ k → B k → Wₙ S (suc n)) (α-iso-step-5-Iso-helper0 a p (suc n)) (u (suc n))
          ≡
        subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a p n) (u n) ∎

      α-iso-step-5-Iso :
        Iso
          (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
            Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
              ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                                  (π (sequence S) ∘ u (suc n))
                                  (u n)))
            (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → X (sequence S) n) ] ((n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)))
      α-iso-step-5-Iso =
        Σ-cong-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ a,p →
          Σ-cong-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 (a,p .fst) (a,p .snd) n)))) λ u →
                              pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → α-iso-step-5-Iso-helper1-Iso (a,p .fst) (a,p .snd) u n)))

      α-iso-step-1-4-Iso-lem-12 :
        Iso (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A)] ((n : ℕ) → a (suc n) ≡ a n)) ]
                  (Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
                      ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                                          (π (sequence S) ∘ u (suc n))
                                          (u n))))
            (limit-of-chain (sequence S))
      fun α-iso-step-1-4-Iso-lem-12 (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
      inv α-iso-step-1-4-Iso-lem-12 x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
      fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = lift tt
      fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = refl i
      snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = refl
      snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = c (suc n)
      leftInv α-iso-step-1-4-Iso-lem-12 (a , b) = refl

shift : ∀ {ℓ} (S : Container ℓ) -> P₀ S (M S) ≡ M S
shift S = isoToPath (shift-iso S) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container ℓ} -> P₀ S (M S) -> M S
in-fun {S = S} = fun (shift-iso S)

out-fun : ∀ {ℓ} {S : Container ℓ} -> M S -> P₀ S (M S)
out-fun {S = S} = inv (shift-iso S)

-- Property of functions into M-types

lift-to-M : ∀ {ℓ} {A : Type ℓ} {S : Container ℓ}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M S)
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container ℓ}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
