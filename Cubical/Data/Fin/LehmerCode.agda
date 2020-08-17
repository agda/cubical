{-# OPTIONS --cubical --no-import-sorts --safe #-}
{-
This module develops Lehmer codes, i.e. an encoding of permutations as finite integers.


-}
module Cubical.Data.Fin.LehmerCode where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Unit as ⊤
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base as F
open import Cubical.Data.Fin.Properties
  renaming (punchOut to punchOutPrim)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)

private
  variable
    n : ℕ

FinExcept : (i : Fin n) → Type₀
FinExcept i = Σ[ j ∈ Fin _ ] ¬ (i ≡ j)

isSetFinExcept : {i : Fin n} → isSet (FinExcept i)
isSetFinExcept = isOfHLevelΣ 2 isSetFin (λ _ → isProp→isSet (isPropΠ (λ _ → ⊥.isProp⊥)))

fsucExc : {i : Fin n} → FinExcept i → FinExcept (fsuc i)
fsucExc {i = i} j = fsuc (fst j) , snd j ∘ fsuc-inj

toFinExc : {i : Fin n} → FinExcept i → Fin n
toFinExc = fst

toFinExc-injective : {i : Fin n} → {j k : FinExcept i} → toFinExc j ≡ toFinExc k → j ≡ k
toFinExc-injective = Σ≡Prop (λ _ → isPropΠ λ _ → ⊥.isProp⊥)

toℕExc : {i : Fin n} → FinExcept i → ℕ
toℕExc = toℕ ∘ toFinExc

toℕExc-injective : {i : Fin n} → {j k : FinExcept i} → toℕExc j ≡ toℕExc k → j ≡ k
toℕExc-injective = toFinExc-injective ∘ toℕ-injective

projectionEquiv : {i : Fin n} → (Unit ⊎ FinExcept i) ≃ Fin n
projectionEquiv {n = n} {i = i} = isoToEquiv goal where
  goal : Iso (Unit ⊎ FinExcept i) (Fin n)
  goal .Iso.fun (inl _) = i
  goal .Iso.fun (inr m) = fst m
  goal .Iso.inv m = case discreteFin i m of λ { (yes _) → inl tt ; (no n) → inr (m , n) }
  goal .Iso.rightInv m with discreteFin i m
  ... | (yes p) = p
  ... | (no _) = toℕ-injective refl
  goal .Iso.leftInv (inl tt) with discreteFin i i
  ... | (yes _) = refl
  ... | (no ¬ii) = ⊥.rec (¬ii refl)
  goal .Iso.leftInv (inr m) with discreteFin i (fst m)
  ... | (yes p) = ⊥.rec (snd m p)
  ... | (no _) = cong inr (toℕExc-injective refl)

punchOut : (i : Fin (suc n)) → FinExcept i → Fin n
punchOut i ¬i = punchOutPrim (snd ¬i)

punchOut-injective : (i : Fin (suc n)) → ∀ j k → punchOut i j ≡ punchOut i k → j ≡ k
punchOut-injective i j k = toFinExc-injective ∘ punchOut-inj (snd j) (snd k)

punchIn : (i : Fin (suc n)) → Fin n → FinExcept i
punchIn {_} i j with fsplit i
...             | inl iz = fsuc j , fznotfs ∘ (iz ∙_)
punchIn {n} i j | inr (i′ , is) with n
...                 | zero = ⊥.rec (¬Fin0 j)
...                 | suc n′ with fsplit j
...                     | inl jz = fzero , fznotfs ∘ sym ∘ (is ∙_)
...                     | inr (j′ , _) =
                            let (k , ¬k≡i′) = punchIn i′ j′
                            in fsuc k , ¬k≡i′ ∘ fsuc-inj ∘ (is ∙_)

punchOut∘In :(i : Fin (suc n)) → ∀ j → punchOut i (punchIn i j) ≡ j
punchOut∘In {_} i j with fsplit i
...                 | inl iz = toℕ-injective refl
punchOut∘In {n} i j | inr (i′ , _) with n
...                     | zero = ⊥.rec (¬Fin0 j)
...                     | suc n′ with fsplit j
...                         | inl jz = toℕ-injective (cong toℕ jz)
...                         | inr (j′ , prfj) =
                              -- the following uses a definitional equality of punchIn but I don't see
                              -- how to sidestep this while using with-abstractions
                              fsuc (punchOut i′ _)               ≡⟨ cong (λ j → fsuc (punchOut i′ j)) (toℕExc-injective refl) ⟩
                              fsuc (punchOut i′ (punchIn i′ j′)) ≡⟨ cong fsuc (punchOut∘In i′ j′) ⟩
                              fsuc j′                            ≡⟨ toℕ-injective (cong toℕ prfj) ⟩
                              j                                  ∎

isEquivPunchOut : {i : Fin (suc n)} → isEquiv (punchOut i)
isEquivPunchOut {i = i} = isEmbedding×isSurjection→isEquiv (isEmbPunchOut , isSurPunchOut) where
  isEmbPunchOut : isEmbedding (punchOut i)
  isEmbPunchOut = injEmbedding isSetFinExcept isSetFin λ {_} {_} → punchOut-injective i _ _
  isSurPunchOut : isSurjection (punchOut i)
  isSurPunchOut b = ∣ _ , punchOut∘In i b ∣

punchOutEquiv : {i : Fin (suc n)} → FinExcept i ≃ Fin n
punchOutEquiv = _ , isEquivPunchOut

infixr 4 _∷_
data LehmerCode : (n : ℕ) → Type₀ where
  [] : LehmerCode zero
  _∷_ : ∀ {n} → Fin (suc n) → LehmerCode n → LehmerCode (suc n)

isContrLehmerZero : isContr (LehmerCode 0)
isContrLehmerZero = [] , λ { [] → refl }

lehmerSucEquiv : Fin (suc n) × LehmerCode n ≃ LehmerCode (suc n)
lehmerSucEquiv = isoToEquiv (iso (λ (e , c) → e ∷ c)
                                 (λ { (e ∷ c) → (e , c) })
                                 (λ { (e ∷ c) → refl })
                                 (λ (e , c) → refl))

lehmerEquiv : (Fin n ≃ Fin n) ≃ LehmerCode n
lehmerEquiv {zero} = isContr→Equiv contrFF isContrLehmerZero where
  contrFF : isContr (Fin zero ≃ Fin zero)
  contrFF = idEquiv _ , λ y → equivEq _ _ (funExt λ f → ⊥.rec (¬Fin0 f))

lehmerEquiv {suc n} =
  (Fin (suc n) ≃ Fin (suc n))                            ≃⟨ isoToEquiv i ⟩
  (Σ[ k ∈ Fin (suc n) ] (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩
  (Fin (suc n) × (Fin n ≃ Fin n))                        ≃⟨ Σ-cong-equiv-snd (λ _ → lehmerEquiv) ⟩
  (Fin (suc n) × LehmerCode n)                           ≃⟨ lehmerSucEquiv ⟩
  LehmerCode (suc n) ■ where
    equivIn : (f : Fin (suc n) ≃ Fin (suc n))
            → FinExcept fzero ≃ FinExcept (equivFun f fzero)
    equivIn f =
      FinExcept fzero
        ≃⟨ Σ-cong-equiv-snd (λ _ → preCompEquiv (invEquiv (congEquiv f))) ⟩
      (Σ[ x ∈ Fin (suc n) ] ¬ ffun fzero ≡ ffun x)
        ≃⟨ Σ-cong-equiv-fst f ⟩
      FinExcept (ffun fzero)
        ■ where ffun = equivFun f

--    equivInChar : ∀ {f} x → fst (equivFun (equivIn f) x) ≡ equivFun f (fst x)
--    equivInChar x = refl

    equivOut : ∀ {k} → FinExcept (fzero {k = n}) ≃ FinExcept k
             → Fin (suc n) ≃ Fin (suc n)
    equivOut {k = k} f =
      Fin (suc n)
        ≃⟨ invEquiv projectionEquiv ⟩
      Unit ⊎ FinExcept fzero
        ≃⟨ isoToEquiv (Sum.sumIso idIso (equivToIso f)) ⟩
      Unit ⊎ FinExcept k
        ≃⟨ projectionEquiv ⟩
      Fin (suc n)
        ■

    equivOutChar : ∀ {k} {f} (x : FinExcept fzero) → equivFun (equivOut {k = k} f) (fst x) ≡ fst (equivFun f x)
    equivOutChar {f = f} x with discreteFin fzero (fst x)
    ... | (yes y) = ⊥.rec (x .snd y)
    ... | (no n) = cong (λ x′ → fst (equivFun f x′)) (toℕExc-injective refl)

    i : Iso (Fin (suc n) ≃ Fin (suc n))
            (Σ[ k ∈ Fin (suc n) ] (FinExcept (fzero {k = n}) ≃ FinExcept k))
    Iso.fun i f = equivFun f fzero , equivIn f
    Iso.inv i (k , f) = equivOut f
    Iso.rightInv i (k , f) = ΣPathP (refl , equivEq _ _ (funExt λ x →
       toℕExc-injective (cong toℕ (equivOutChar {f = f} x))))
    Iso.leftInv i f = equivEq _ _ (funExt goal) where
      goal : ∀ x → equivFun (equivOut (equivIn f)) x ≡ equivFun f x
      goal x = case fsplit x return (λ _ → equivFun (equivOut (equivIn f)) x ≡ equivFun f x) of λ
        { (inl xz) → subst (λ x → equivFun (equivOut (equivIn f)) x ≡ equivFun f x) xz refl
        ; (inr (_ , xn)) → equivOutChar {f = equivIn f} (x , fznotfs ∘ (_∙ sym xn))
        }

    ii : ∀ k → (FinExcept fzero ≃ FinExcept k) ≃ (Fin n ≃ Fin n)
    ii k = (FinExcept fzero ≃ FinExcept k) ≃⟨ cong≃ (λ R → FinExcept fzero ≃ R) punchOutEquiv ⟩
           (FinExcept fzero ≃ Fin n)       ≃⟨ cong≃ (λ L → L ≃ Fin n) punchOutEquiv  ⟩
           (Fin n ≃ Fin n)                 ■

encode : (Fin n ≃ Fin n) → LehmerCode n
encode = equivFun lehmerEquiv

decode : LehmerCode n → Fin n ≃ Fin n
decode = invEq lehmerEquiv

factorial : ℕ → ℕ
factorial zero = 1
factorial (suc n) = suc n * factorial n

lehmerFinEquiv : LehmerCode n ≃ Fin (factorial n)
lehmerFinEquiv {zero} = isContr→Equiv isContrLehmerZero isContrFin1
lehmerFinEquiv {suc n} = _ ≃⟨ invEquiv lehmerSucEquiv ⟩
                         _ ≃⟨ ≃-× (idEquiv _) lehmerFinEquiv ⟩
                         _ ≃⟨ factorEquiv ⟩
                         _ ■

private
  -- this example is copied from wikipedia, using the permutation of the letters A-G
  -- B,F,A,G,D,E,C
  -- given by the corresponding Lehmer code of
  -- 1 4 0 3 1 1 0
  exampleCode : LehmerCode 7
  exampleCode = (1 , (5 , refl)) ∷ (4 , (1 , refl)) ∷ (0 , (4 , refl)) ∷ (3 , (0 , refl)) ∷ (1 , (1 , refl)) ∷ (1 , (0 , refl)) ∷ (0 , (0 , refl)) ∷ []

  example : Fin 7 ≃ Fin 7
  example = decode exampleCode

  -- C should decode to G
  computation : fst (equivFun example (3 , (3 , refl))) ≡ 6
  computation = refl

  _ : toℕ (equivFun lehmerFinEquiv exampleCode) ≡ 4019
  _ = refl
