module Cubical.Data.Nat.Logarithm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum   as ⊎

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Nat.Mod renaming (
  remainder_/_ to _%_ ; quotient_/_ to _/_ ; ≡remainder+quotient to ≡%+·/)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Nullary

open <-≤-Reasoning ℕ
  (snd ℕ≤Poset) (snd ℕ<Quoset) (λ _ → <≤-trans) (λ _ → ≤<-trans) <-weaken
open ≤-syntax
open <-syntax
open ≡-syntax

record Logℕ (b x : ℕ) : Type where
  no-eta-equality
  field
    log     : ℕ
    ^log≤   : b ^ log ≤ x
    <^1+log : x < b ^ suc log

unquoteDecl LogℕIsoΣ = declareRecordIsoΣ LogℕIsoΣ (quote Logℕ)

private
  lemmaIsPropLogℕ : ∀ {m x l₀ l₁} → x < (suc m) ^ suc l₀ → (suc m) ^ l₁ ≤ x → ¬ (l₀ < l₁)
  lemmaIsPropLogℕ {b-1} {x} {l₀} {l₁} <b^1+l₀ b^l₁≤ l₀<l₁ =
    let b = suc b-1
    in  <-irrefl $ begin< x <⟨ <b^1+l₀ ⟩ b ^ suc l₀ ≤⟨ ≤-^ˡ l₀<l₁ ⟩ b ^ l₁ ≤⟨ b^l₁≤ ⟩ x ◾

isPropLogℕ : ∀ m n → isProp (Logℕ (suc m) n)
isPropLogℕ m x = isOfHLevelRetractFromIso 1 LogℕIsoΣ proof where
  proof : isProp (Σ[ l ∈ ℕ ] ((suc m) ^ l ≤ x) × (x < (suc m) ^ suc l))
  proof (l₀ , b^l₀≤ , <b^1+l₀) (l₁ , b^l₁≤ , <b^1+l₁) with l₀ ≟ l₁
  ... | lt l₀<l₁ = ⊥.rec  (lemmaIsPropLogℕ <b^1+l₀ b^l₁≤ l₀<l₁)
  ... | eq l₀≡l₁ = Σ≡Prop (λ _ → isProp× isProp≤ isProp≤) l₀≡l₁
  ... | gt l₀>l₁ = ⊥.rec  (lemmaIsPropLogℕ <b^1+l₁ b^l₀≤ l₀>l₁)

module LogTheory (logℕ : ∀ m n → Logℕ (suc (suc m)) (suc n)) where

  log : (b : ℕ) → {2 ≤ᵗ b} → (x : ℕ) → {1 ≤ᵗ x} → ℕ
  log (suc (suc m)) (suc n) = Logℕ.log (logℕ m n)

  module _ (m : ℕ) where
    private
      b   = suc (suc m)
      b-1 = suc m

      logℕBase^ : ∀ n → Logℕ b (b ^ n)
      logℕBase^ n .Logℕ.log     = n
      logℕBase^ n .Logℕ.^log≤   = ≤-refl
      logℕBase^ n .Logℕ.<^1+log = <-^ˡ {m = n} <-suc

      logℕBase· : ∀ n → Logℕ b (b · suc n)
      logℕBase· n .Logℕ.log     = suc (log b (suc n))
      logℕBase· n .Logℕ.^log≤   = ≤-·ˡ {k = b}     (Logℕ.^log≤ (logℕ m n))
      logℕBase· n .Logℕ.<^1+log = <-·ˡ {k = suc m} (Logℕ.<^1+log (logℕ m n))

      logℕ1 : Logℕ b 1
      logℕ1 .Logℕ.log     = 0
      logℕ1 .Logℕ.^log≤   = ≤-refl
      logℕ1 .Logℕ.<^1+log = suc-≤-suc zero-<suc

    isContrLogℕ : ∀ x → {1 ≤ᵗ x} → isContr (Logℕ (suc (suc m)) x)
    isContrLogℕ (suc n) .fst = logℕ m n
    isContrLogℕ (suc n) .snd = isPropLogℕ (suc m) (suc n) (logℕ m n)

    isUniqueLogℕ : ∀ {n} → {1≤n : 1 ≤ᵗ n} → (q : Logℕ b n) → log b n {1≤n} ≡ (Logℕ.log q)
    isUniqueLogℕ {suc n} = cong Logℕ.log ∘ snd (isContrLogℕ _)

    logBase^ : ∀ n → log b (b ^ n) {<→<ᵗ (0<^ n)} ≡ n
    logBase^ = isUniqueLogℕ ∘ logℕBase^

    logBase· : ∀ n → log b (b · suc n) ≡ suc (log b (suc n))
    logBase· = isUniqueLogℕ ∘ logℕBase·

    log1 : log b 1 ≡ 0
    log1 = isUniqueLogℕ logℕ1

    logBase : log b b ≡ 1
    logBase =
      cong (λ m → log b (suc m)) (sym (·-identityʳ b-1)) ∙∙ logBase· 0 ∙∙ cong suc log1

    logMono≤ : ∀ x y {1≤x} {1≤y} → x ≤ y → log b x {1≤x} ≤ log b y {1≤y}
    logMono≤ x@(suc x') y@(suc y') x≤y = pred-≤-pred $ <-^-cancelˡ {k = m} $ begin<
      b ^ log b x       ≤⟨ Logℕ.^log≤ (logℕ m x') ⟩
      x                 ≤⟨ x≤y ⟩
      y                 <⟨ Logℕ.<^1+log (logℕ m y') ⟩
      b ^ suc (log b y) ◾

module LogCore (m : ℕ) where
  private
    b   = suc (suc m)
    b-1 = suc m

    /b≤f : ∀ n {f} → n ≤ᵗ f → (suc n / b) ≤ᵗ f
    /b≤f n {f} n≤f =
      ≤→≤ᵇ (begin< suc n / b <⟨ quotient<id n m ⟩ suc n ≤⟨ ≤ᵇ→≤ n≤f ⟩ suc f ◾)

  hlog : ∀ n f → n ≤ᵗ f → ℕ
  hlog   zero    f       n≤f = 0
  hlog x@(suc n) (suc f) n≤f with Dichotomyℕ b x
  ... | inl b≤x = suc (hlog (x / b) f (/b≤f n n≤f))
  ... | inr x<b = 0

  <base→hlog≡0 : ∀ {x f} → {t : x ≤ᵗ f} → (x < b) → hlog x f t ≡ 0
  <base→hlog≡0   {zero}  {f}     x<b = refl
  <base→hlog≡0 x@{suc n} {suc f} x<b with Dichotomyℕ b x
  ... | inl b≤x = ⊥.rec (<-asym x<b b≤x)
  ... | inr x<b = refl

  ^hlog≤ : ∀ x f → {1 ≤ᵗ x} → (t : x ≤ᵗ f) → b ^ (hlog x f t) ≤ x
  ^hlog≤ x@(suc n) (suc f) t with Dichotomyℕ b x
  ... | inr x<b = ≤ᵇ→≤ tt
  ... | inl b≤x with Dichotomyℕ b (x / b)
  ... | inl b≤x/b = let 1≤x/b = ≤→≤ᵇ (≥→quotient≥1 n b-1 b≤x) in begin≤
    b ^ suc (hlog (x / b) f (/b≤f n t))   ≤⟨ ≤-·ˡ {k = b} (^hlog≤ (x / b) f {1≤x/b} _) ⟩
    b · (x / b)                           ≤⟨ ≤SumRight {k = x % b} ⟩
    x % b + b · (x / b)                 ≡→≤⟨ ≡%+·/ b x ⟩
    x                                     ◾
  ... | inr x/b<b = flip (subst (_≤ x)) b≤x $
    b                                   ≡⟨ sym (·-identityʳ b) ⟩
    b · b ^ 0                           ≡⟨ sym (cong (b ^_ ∘ suc) (<base→hlog≡0 x/b<b)) ⟩
    b ^ suc (hlog (x / b) f (/b≤f n t)) ∎

  <^1+hlog : ∀ x f → (t : x ≤ᵗ f) → x < b ^ suc (hlog x f t)
  <^1+hlog   0       f       t = 0<^ {b-1} 1
  <^1+hlog x@(suc n) (suc f) t with Dichotomyℕ b x
  ... | inl b≤x = quotient<→<· _ b-1 _ (<^1+hlog (x / b) f (/b≤f n t))
  ... | inr x<b = subst (x <_) (sym (·-identityʳ b)) x<b

logℕ : ∀ m n → Logℕ (suc (suc m)) (suc n)
logℕ m n .Logℕ.log     = LogCore.hlog     m (suc n) (suc n) (<ᵗsucm {n})
logℕ m n .Logℕ.^log≤   = LogCore.^hlog≤   m (suc n) (suc n) (<ᵗsucm {n})
logℕ m n .Logℕ.<^1+log = LogCore.<^1+hlog m (suc n) (suc n) (<ᵗsucm {n})

open LogTheory (logℕ) public

-- we prove this lemma here rather than in the `LogTheory` module,
-- as it follows immediately from an auxiliary result used to define `logℕ`
<base→log≡0 : ∀ m x {1<x} → (x < suc (suc m)) → log (suc (suc m)) x {1<x} ≡ 0
<base→log≡0 m (suc n) = LogCore.<base→hlog≡0 m
