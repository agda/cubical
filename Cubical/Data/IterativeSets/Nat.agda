-- This module provides the Von-Neumann encoding of the natural numbers
-- i.e. 0 = ∅, suc n = n ⊎ {n}

module Cubical.Data.IterativeSets.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; elim* to ⊥*-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Fin as Fin
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum using (_⊎_; inl; inr; ⊎-IdL-⊥*-≃) public
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Homotopy.Base

open import Cubical.Data.IterativeMultisets.Base renaming (index to index-∞ ; elements to elements-V∞)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

-- suc x = x ⊎ {x}
suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ {ℓ} (sup-∞ A f , isitsetAf) = fromEmb E
    where
        ϕₓ : (index (sup-∞ A f , isitsetAf) ⊎ Unit* {ℓ}) → V⁰ {ℓ}
        ϕₓ (inl a) = f a , isitsetAf .snd a
        ϕₓ (inr _) = (sup-∞ A f , isitsetAf)

        eqFib : (z : V⁰ {ℓ}) → (fiber ϕₓ z ≃
                  ((z ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ z)))
        eqFib (sup-∞ B g , isitsetBg) = isoToEquiv (iso to fro sec ret)
            where
                to : fiber ϕₓ (sup-∞ B g , isitsetBg) →
                      ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf))
                        ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg))
                to (inl a , p) = inl (a , p)
                to (inr _ , p) = inr p

                fro : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf))
                        ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg))
                        → fiber ϕₓ (sup-∞ B g , isitsetBg)
                fro (inl (a , p)) = inl a , p
                fro (inr p) = inr _ , p

                sec : section to fro
                sec (inl _) = refl
                sec (inr _) = refl
                ret : retract to fro
                ret (inl _ , _) = refl
                ret (inr _ , _) = refl
        hpf : hasPropFibers ϕₓ
        hpf (sup-∞ B g , isitsetBg) = isOfHLevelRespectEquiv 1
                (invEquiv (eqFib (sup-∞ B g , isitsetBg)))
                (isProp⊎ (isEmbedding→hasPropFibers
                           (isEmbedding-elements (sup-∞ A f , isitsetAf))
                           (sup-∞ B g , isitsetBg)) (isSetV⁰ _ _) (curry ∈⁰×≡→⊥))
            where
                ∈⁰×≡→⊥ : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf))
                           × ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg)) → ⊥
                ∈⁰×≡→⊥ ((a , pa) , p) = ∈⁰-irrefl {x = (sup-∞ B g , isitsetBg)}
                           (transport (cong (λ r → ((sup-∞ B g , isitsetBg) ∈⁰ r)) p) (a , pa))

        E : Embedding (V⁰ {ℓ}) ℓ
        E .fst = A ⊎ Unit* {ℓ}
        E .snd .fst = ϕₓ
        E .snd .snd = hasPropFibers→isEmbedding hpf

vonNeumannEncoding : ℕ* {ℓ} → V⁰ {ℓ}
vonNeumannEncoding (lift zero) = empty⁰
vonNeumannEncoding (lift (suc x)) = suc⁰ (vonNeumannEncoding (lift x))

El⁰-suc⁰≡El⁰⊎Unit* : {x : V⁰ {ℓ}} → El⁰ {ℓ} (suc⁰ x) ≡ (El⁰ x ⊎ Unit* {ℓ})
El⁰-suc⁰≡El⁰⊎Unit* {x = (sup-∞ _ _ , _)} = refl

El⁰-vNE-suc≡El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n)))
                                      ≡ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
El⁰-vNE-suc≡El⁰-vNE⊎Unit* n = El⁰-suc⁰≡El⁰⊎Unit* {x = vonNeumannEncoding (lift n)}

El⁰-vNE-suc≃El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n)))
                                      ≃ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
El⁰-vNE-suc≃El⁰-vNE⊎Unit* = pathToEquiv ∘ El⁰-vNE-suc≡El⁰-vNE⊎Unit*

private
  module _ where
    fsuc-predFin-ret : (m : ℕ) → retract (fsuc {k = suc m}) (predFin m)
    fsuc-predFin-ret _ (zero , _) = refl
    fsuc-predFin-ret _ (suc _ , _) = refl

    fsuc-predFin-quasi-sec : (m : ℕ) → (x : Fin (suc (suc m)))
                              → ¬ x ≡ fzero → fsuc (predFin m x) ≡ x
    fsuc-predFin-quasi-sec _ (zero , _) x≢0 = ⊥-elim (x≢0 refl)
    fsuc-predFin-quasi-sec _ (suc _ , _) _ = refl

-- the von-Neumann encoding of `n` is precisely a finite set with `n` elements
vonNeumannindex≃Fin : (n : ℕ) → (El⁰ (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin n)
vonNeumannindex≃Fin {ℓ} = elim+2 case0 case1 caseSuc
  where
    case0 : El⁰ (vonNeumannEncoding (lift 0)) ≃ Fin 0
    case0 = uninhabEquiv (λ ()) ¬Fin0

    case1 : El⁰ (vonNeumannEncoding (lift 1)) ≃ Fin 1
    case1 = compEquiv (compEquiv ⊎-IdL-⊥*-≃ (invEquiv LiftEquiv)) Unit≃Fin1

    caseSuc : (n : ℕ) → El⁰ (vonNeumannEncoding (lift (suc n))) ≃ Fin (suc n) →
                          El⁰ (vonNeumannEncoding (lift (suc (suc n)))) ≃ Fin (suc (suc n))
    caseSuc n indHyp = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc n)) (isoToEquiv isom)
      where
        isom : Iso (El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit*) (Fin (suc (suc n)))
        isom .Iso.fun (inl x) = fsuc (indHyp .fst x)
        isom .Iso.fun (inr x) = fzero
        isom .Iso.inv (zero , _) = inr tt*
        isom .Iso.inv (suc m , sucm<sucsucn) = inl (invEq indHyp (predFin n (suc m , sucm<sucsucn)))
        isom .Iso.sec (zero , _) = refl
        isom .Iso.sec (suc m , sucm<sucsucn) = cong fsuc (secEq indHyp (predFin n (suc m , sucm<sucsucn)))
                                                ∙ fsuc-predFin-quasi-sec n (suc m , sucm<sucsucn) λ p → fznotfs (sym p)
        isom .Iso.ret (inl x) = cong inl (retEq indHyp x)
        isom .Iso.ret (inr x) = refl

ℕ⁰ : V⁰ {ℓ}
ℕ⁰ {ℓ} = fromEmb E
    where
        isinj : (w x : ℕ* {ℓ}) → vonNeumannEncoding w ≡ vonNeumannEncoding x → w ≡ x
        isinj (lift n) (lift m) p = liftExt (Fin-inj n m (ua (compEquiv
                                      (invEquiv (vonNeumannindex≃Fin n))
                                      (compEquiv (pathToEquiv (cong index p)) (vonNeumannindex≃Fin m)))))
        E : Embedding (V⁰ {ℓ}) ℓ
        E .fst = ℕ* {ℓ}
        E .snd .fst = vonNeumannEncoding {ℓ}
        E .snd .snd = injEmbedding isSetV⁰ (λ {w} {x} → isinj w x)

ℕ⁰Isℕ* : El⁰ (ℕ⁰ {ℓ}) ≡ ℕ* {ℓ}
ℕ⁰Isℕ* = refl
