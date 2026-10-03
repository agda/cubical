module Cubical.Data.Nat.Root where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.BinarySearch

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

record Rootℕ (n x : ℕ) : Type where
  no-eta-equality
  field
    ⌊_√_⌋  : ℕ
    √^≤   : ⌊_√_⌋ ^ n ≤ x
    <1+√^ : x < (suc ⌊_√_⌋) ^ n

unquoteDecl RootℕIsoΣ = declareRecordIsoΣ RootℕIsoΣ (quote Rootℕ)

private
  lemmaIsPropRootℕ : ∀ n {x r₀ r₁} → x < suc r₀ ^ n → r₁ ^ n ≤ x → ¬ (r₀ < r₁)
  lemmaIsPropRootℕ n {x} {r₀} {r₁} <1+r₀^n r₁^n≤ r₀<r₁ = <-irrefl $
    begin< x <⟨ <1+r₀^n ⟩ suc r₀ ^ n ≤⟨ ≤-^ʳ {k = n} r₀<r₁ ⟩ r₁ ^ n ≤⟨ r₁^n≤ ⟩ x ◾

isPropRootℕ : ∀ n x → isProp (Rootℕ n x)
isPropRootℕ n x = isOfHLevelRetractFromIso 1 RootℕIsoΣ proof where
  proof : isProp (Σ[ r ∈ ℕ ] (r ^ n ≤ x) × (x < suc r ^ n))
  proof (r₀ , r₀^n≤ , <1+r₀^n) (r₁ , r₁^n≤ , <1+r₁^n) with r₀ ≟ r₁
  ... | lt r₀<r₁ = ⊥.rec  (lemmaIsPropRootℕ n <1+r₀^n r₁^n≤ r₀<r₁)
  ... | eq r₀≡r₁ = Σ≡Prop (λ _ → isProp× isProp≤ isProp≤) r₀≡r₁
  ... | gt r₀>r₁ = ⊥.rec  (lemmaIsPropRootℕ n <1+r₁^n r₀^n≤ r₀>r₁)

module RootTheory (rootℕ : ∀ n x → Rootℕ (suc n) x) where
  ⌊_√_⌋ : (b : ℕ) → {1 ≤ᵗ b} → ℕ → ℕ
  ⌊_√_⌋ (suc n) x = Rootℕ.⌊_√_⌋ (rootℕ n x)

  module _ (n-1 : ℕ) where
    private
      n = suc n-1

      rootℕ^Exponent : ∀ x → Rootℕ n (x ^ n)
      rootℕ^Exponent x .Rootℕ.⌊_√_⌋  = x
      rootℕ^Exponent x .Rootℕ.√^≤   = ≤-refl
      rootℕ^Exponent x .Rootℕ.<1+√^ = <-^ʳ {k = n-1} <-suc

      rootℕ0 : Rootℕ n 0
      rootℕ0 .Rootℕ.⌊_√_⌋  = 0
      rootℕ0 .Rootℕ.√^≤   = zero-≤
      rootℕ0 .Rootℕ.<1+√^ = 0<^ n

      rootℕ1 : Rootℕ n 1
      rootℕ1 .Rootℕ.⌊_√_⌋  = 1
      rootℕ1 .Rootℕ.√^≤   = subst (_≤ 1) (sym (1^≡1 n)) ≤-refl
      rootℕ1 .Rootℕ.<1+√^ = 1<^suc n-1

    isContrRootℕ : ∀ x → isContr (Rootℕ n x)
    isContrRootℕ x .fst = rootℕ n-1 x
    isContrRootℕ x .snd = isPropRootℕ n x (rootℕ n-1 x)

    isUniqueRootℕ : ∀ {x} → (q : Rootℕ n x) → ⌊ n √ x ⌋ ≡ (Rootℕ.⌊_√_⌋ q)
    isUniqueRootℕ = cong Rootℕ.⌊_√_⌋ ∘ snd (isContrRootℕ _)

    root^Exponent : ∀ x → ⌊ n √ x ^ n ⌋ ≡ x
    root^Exponent = isUniqueRootℕ ∘ rootℕ^Exponent

    root0 : ⌊ n √ 0 ⌋ ≡ 0
    root0 = isUniqueRootℕ rootℕ0

    root1 : ⌊ n √ 1 ⌋ ≡ 1
    root1 = isUniqueRootℕ rootℕ1

    √Mono≤ : ∀ x y → x ≤ y → ⌊ n √ x ⌋ ≤ ⌊ n √ y ⌋
    √Mono≤ x y x≤y = <-asym' λ √y<√x → flip <-asym (≤-^ʳ {k = n} √y<√x) $ begin<
      ⌊ n √ x ⌋ ^ n      ≤⟨ Rootℕ.√^≤ (rootℕ n-1 x) ⟩
      x                 ≤⟨ x≤y ⟩
      y                 <⟨ Rootℕ.<1+√^ (rootℕ n-1 y) ⟩
      suc ⌊ n √ y ⌋ ^ n ◾

module RootCore (n-1 x : ℕ) where
  private
    n = suc n-1
    Σ<ⁿ : Σ[ k ∈ ℕ ] x <ᵗ k ^ n
    Σ<ⁿ = (suc x , <→<ᵗ (L≤^suc (suc x) n-1))
  open BiggestImage≤.→Biggest (_^ n) (≤-^ʳ {k = n}) refl x Σ<ⁿ public renaming
    (preimage to ⌊1+_√_⌋ ; <imageSuc to <1+⌊1+_√_⌋^ ; image≤ to ⌊1+_√_⌋^≤)

rootℕ : ∀ n-1 x → Rootℕ (suc n-1) x
rootℕ n-1 x .Rootℕ.⌊_√_⌋  = RootCore.⌊1+ n-1 √ x ⌋
rootℕ n-1 x .Rootℕ.√^≤   = RootCore.⌊1+ n-1 √ x ⌋^≤
rootℕ n-1 x .Rootℕ.<1+√^ = RootCore.<1+⌊1+ n-1 √ x ⌋^

open RootTheory (rootℕ) public

⌊√_⌋ ⌊³√_⌋ : ℕ → ℕ
⌊√_⌋  = ⌊ 2 √_⌋
⌊³√_⌋ = ⌊ 3 √_⌋

private
  _ : ⌊√ 64 ⌋ ≡ 8
  _ = refl

  _ : ⌊√ 63 ⌋ ≡ 7
  _ = refl

  _ : ⌊√ 65 ⌋ ≡ 8
  _ = refl

  _ : ⌊³√ 64 ⌋ ≡ 4
  _ = refl

  toDigits : (n : ℕ) → {1 ≤ᵗ n} → ℕ → ℕ → ℕ × ℕ
  toDigits n@(suc n-1) x d =
    let root = ⌊ n √ x · (10 ^ n) ^ d ⌋
    in quotient root / (10 ^ d) , remainder root / (10 ^ d)

  √2Digits  = toDigits 2 2
  ³√2Digits = toDigits 3 2

  _ : √2Digits 20 ≡ (1 , 41421356237309504880)
  _ = refl

  _ : ³√2Digits 20 ≡ (1 , 25992104989487316476)
  _ = refl
