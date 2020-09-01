{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Fin.Properties where

open import Cubical.Core.Everything

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Data.Fin.Base as Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

private
 variable
   a b ℓ : Level
   n : ℕ
   A : Type a

-- Fin 0 is empty, and thus a proposition.
isPropFin0 : isProp (Fin 0)
isPropFin0 = Empty.rec ∘ ¬Fin0

-- Fin 1 has only one value.
isContrFin1 : isContr (Fin 1)
isContrFin1
  = fzero , λ
  { (zero , _) → toℕ-injective refl
  ; (suc k , sk<1) → Empty.rec (¬-<-zero (pred-≤-pred sk<1))
  }

Unit≃Fin1 : Unit ≃ Fin 1
Unit≃Fin1 =
  isoToEquiv
    (iso
      (const fzero)
      (const tt)
      (isContrFin1 .snd)
      (isContrUnit .snd)
    )

-- Regardless of k, Fin k is a set.
isSetFin : ∀{k} → isSet (Fin k)
isSetFin {k} = isSetΣ isSetℕ (λ _ → isProp→isSet m≤n-isProp)

discreteFin : ∀ {n} → Discrete (Fin n)
discreteFin {n} (x , hx) (y , hy) with discreteℕ x y
... | yes prf = yes (Σ≡Prop (λ _ → m≤n-isProp) prf)
... | no prf = no λ h → prf (cong fst h)

inject<-ne : ∀ {n} (i : Fin n) → ¬ inject< ≤-refl i ≡ (n , ≤-refl)
inject<-ne {n} (k , k<n) p = <→≢ k<n (cong fst p)

Fin-fst-≡ : ∀ {n} {i j : Fin n} → fst i ≡ fst j → i ≡ j
Fin-fst-≡ = Σ≡Prop (λ _ → m≤n-isProp)

private
  subst-app : (B : A → Type b) (f : (x : A) → B x) {x y : A} (x≡y : x ≡ y) →
              subst B x≡y (f x) ≡ f y
  subst-app B f {x = x} =
    J (λ y e → subst B e (f x) ≡ f y) (substRefl {B = B} (f x))

-- Computation rules for the eliminator.
module _ (P : ∀ {k} → Fin k → Type ℓ)
         (fz : ∀ {k} → P {suc k} fzero)
         (fs : ∀ {k} {fn : Fin k} → P fn → P (fsuc fn))
         {k : ℕ} where
  elim-fzero : Fin.elim P fz fs {k = suc k} fzero ≡ fz
  elim-fzero =
    subst P (toℕ-injective _) fz ≡⟨ cong (λ p → subst P p fz) (isSetFin _ _ _ _) ⟩
    subst P refl fz              ≡⟨ substRefl {B = P} fz ⟩
    fz                           ∎

  elim-fsuc : (fk : Fin k) → Fin.elim P fz fs (fsuc fk) ≡ fs (Fin.elim P fz fs fk)
  elim-fsuc fk =
    subst P (toℕ-injective (λ _ → toℕ (fsuc fk′))) (fs (Fin.elim P fz fs fk′))
      ≡⟨ cong (λ p → subst P p (fs (Fin.elim P fz fs fk′)) ) (isSetFin _ _ _ _) ⟩
    subst P (cong fsuc fk′≡fk) (fs (Fin.elim P fz fs fk′))
      ≡⟨ subst-app _ (λ fj → fs (Fin.elim P fz fs fj)) fk′≡fk ⟩
    fs (Fin.elim P fz fs fk)
      ∎
    where
    fk′ = fst fk , pred-≤-pred (snd (fsuc fk))
    fk′≡fk : fk′ ≡ fk
    fk′≡fk = toℕ-injective refl

-- Helper function for the reduction procedure below.
--
-- If n = expand o k m, then n is congruent to m modulo k.
expand : ℕ → ℕ → ℕ → ℕ
expand 0 k m = m
expand (suc o) k m = k + expand o k m

expand≡ : ∀ k m o → expand o k m ≡ o * k + m
expand≡ k m zero = refl
expand≡ k m (suc o)
  = cong (k +_) (expand≡ k m o) ∙ +-assoc k (o * k) m

-- Expand a pair. This is useful because the whole function is
-- injective.
expand× : ∀{k} → (Fin k × ℕ) → ℕ
expand× {k} (f , o) = expand o k (toℕ f)

private
  lemma₀ : ∀{k m n r} → r ≡ n → k + m ≡ n → k ≤ r
  lemma₀ {k = k} {m} p q = m , +-comm m k ∙ q ∙ sym p

  expand×Inj : ∀ k → {t1 t2 : Fin (suc k) × ℕ} → expand× t1 ≡ expand× t2 → t1 ≡ t2
  expand×Inj k {f1 , zero} {f2 , zero} p i
    = toℕ-injective {fj = f1} {f2} p i , zero
  expand×Inj k {f1 , suc o1} {(r , r<sk) , zero} p
    = Empty.rec (<-asym r<sk (lemma₀ refl p))
  expand×Inj k {(r , r<sk) , zero} {f2 , suc o2} p
    = Empty.rec (<-asym r<sk (lemma₀ refl (sym p)))
  expand×Inj k {f1 , suc o1} {f2 , suc o2}
    = cong (λ { (f , o) → (f , suc o) })
    ∘ expand×Inj k {f1 , o1} {f2 , o2}
    ∘ inj-m+ {suc k}

  expand×Emb : ∀ k → isEmbedding (expand× {k})
  expand×Emb 0 = Empty.rec ∘ ¬Fin0 ∘ fst
  expand×Emb (suc k)
    = injEmbedding (isSetΣ isSetFin (λ _ → isSetℕ)) isSetℕ (expand×Inj k)

-- A Residue is a family of types representing evidence that a
-- natural is congruent to a value of a finite type.
Residue : ℕ → ℕ → Type₀
Residue k n = Σ[ tup ∈ Fin k × ℕ ] expand× tup ≡ n

-- There is at most one canonical finite value congruent to each
-- natural.
isPropResidue : ∀ k n → isProp (Residue k n)
isPropResidue k = isEmbedding→hasPropFibers (expand×Emb k)

-- A value of a finite type is its own residue.
Fin→Residue : ∀{k} → (f : Fin k) → Residue k (toℕ f)
Fin→Residue f = (f , 0) , refl

-- Fibers of numbers that differ by k are equivalent in a more obvious
-- way than via the fact that they are propositions.
Residue+k : (k n : ℕ) → Residue k n → Residue k (k + n)
Residue+k k n ((f , o) , p) = (f , suc o) , cong (k +_) p

Residue-k : (k n : ℕ) → Residue k (k + n) → Residue k n
Residue-k k n (((r , r<k) , zero) , p) = Empty.rec (<-asym r<k (lemma₀ p refl))
Residue-k k n ((f , suc o) , p) = ((f , o) , inj-m+ p)

Residue+k-k
  : (k n : ℕ)
  → (R : Residue k (k + n))
  → Residue+k k n (Residue-k k n R) ≡ R
Residue+k-k k n (((r , r<k) , zero) , p) = Empty.rec (<-asym r<k (lemma₀ p refl))
Residue+k-k k n ((f , suc o) , p)
  = Σ≡Prop (λ tup → isSetℕ (expand× tup) (k + n)) refl

Residue-k+k
  : (k n : ℕ)
  → (R : Residue k n)
  → Residue-k k n (Residue+k k n R) ≡ R
Residue-k+k k n ((f , o) , p)
  = Σ≡Prop (λ tup → isSetℕ (expand× tup) n) refl

private
  Residue≃ : ∀ k n → Residue k n ≃ Residue k (k + n)
  Residue≃ k n
    = Residue+k k n
    , isoToIsEquiv (iso (Residue+k k n) (Residue-k k n)
                        (Residue+k-k k n) (Residue-k+k k n))

Residue≡ : ∀ k n → Residue k n ≡ Residue k (k + n)
Residue≡ k n = ua (Residue≃ k n)

-- For positive `k`, all `n` have a canonical residue mod `k`.
module Reduce (k₀ : ℕ) where
  k : ℕ
  k = suc k₀

  base : ∀ n (n<k : n < k) → Residue k n
  base n n<k = Fin→Residue (n , n<k)

  step : ∀ n → Residue k n → Residue k (k + n)
  step n = transport (Residue≡ k n)

  reduce : ∀ n → Residue k n
  reduce = +induction k₀ (Residue k) base step

  reduce≡
    : ∀ n → transport (Residue≡ k n) (reduce n) ≡ reduce (k + n)
  reduce≡ n
    = sym (+inductionStep k₀ _ base step n)

  reduceP
    : ∀ n → PathP (λ i → Residue≡ k n i) (reduce n) (reduce (k + n))
  reduceP n = toPathP (reduce≡ n)

open Reduce using (reduce; reduce≡) public

extract : ∀{k n} → Residue k n → Fin k
extract = fst ∘ fst

private
  lemma₅
    : ∀ k n (R : Residue k n)
    →  extract R ≡ extract (transport (Residue≡ k n) R)
  lemma₅ k n = sym ∘ cong extract ∘ uaβ (Residue≃ k n)

-- The residue of n modulo k is the same as the residue of k + n.
extract≡ : ∀ k n → extract (reduce k n) ≡ extract (reduce k (suc k + n))
extract≡ k n
  = lemma₅ (suc k) n (reduce k n) ∙ cong extract (Reduce.reduce≡ k n)

isContrResidue : ∀{k n} → isContr (Residue (suc k) n)
isContrResidue {k} {n} = inhProp→isContr (reduce k n) (isPropResidue (suc k) n)

-- the modulo operator on ℕ

_%_ : ℕ → ℕ → ℕ
n % zero = n
n % (suc k) = toℕ (extract (reduce k n))

_/_ : ℕ → ℕ → ℕ
n / zero = zero
n / (suc k) = reduce k n .fst .snd

moddiv : ∀ n k → (n / k) * k + n % k ≡ n
moddiv n zero = refl
moddiv n (suc k) = sym (expand≡ _ _ (n / suc k)) ∙ reduce k n .snd

n%k≡n[modk] : ∀ n k → Σ[ o ∈ ℕ ] o * k + n % k ≡ n
n%k≡n[modk] n k = (n / k) , moddiv n k

n%sk<sk : (n k : ℕ) → (n % suc k) < suc k
n%sk<sk n k = extract (reduce k n) .snd

fznotfs : ∀ {m : ℕ} {k : Fin m} → ¬ fzero ≡ fsuc k
fznotfs {m} p = subst F p tt
  where
    F : Fin (suc m) → Type₀
    F (zero , _) = Unit
    F (suc _ , _) = ⊥

fsuc-inj : {fj fk : Fin n} → fsuc fj ≡ fsuc fk → fj ≡ fk
fsuc-inj = toℕ-injective ∘ injSuc ∘ cong toℕ

punchOut : ∀ {m} {i j : Fin (suc m)} → (¬ i ≡ j) → Fin m
punchOut {_} {i} {j} p with fsplit i | fsplit j
punchOut {_} {i} {j} p | inl prfi | inl prfj =
  Empty.elim (p (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfj ⟩ j ∎))
punchOut {_} {i} {j} p | inl prfi | inr (kj , prfj) =
  kj
punchOut {zero} {i} {j} p  | inr (ki , prfi) | inl prfj =
  Empty.elim (p (
    i ≡⟨ sym (isContrFin1 .snd i) ⟩
    c ≡⟨ isContrFin1 .snd j ⟩
    j ∎
  ))
  where c = isContrFin1 .fst
punchOut {suc _} {i} {j} p | inr (ki , prfi) | inl prfj =
  fzero
punchOut {zero} {i} {j} p | inr (ki , prfi) | inr (kj , prfj) =
  Empty.elim ((p (
    i ≡⟨ sym (isContrFin1 .snd i) ⟩
    c ≡⟨ isContrFin1 .snd j ⟩
    j ∎)
  ))
  where c = isContrFin1 .fst
punchOut {suc _} {i} {j} p | inr (ki , prfi) | inr (kj , prfj) =
  fsuc (punchOut {i = ki} {j = kj}
    (λ q → p (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kj ≡⟨ prfj ⟩ j ∎))
  )

punchOut-inj
  : ∀ {m} {i j k : Fin (suc m)} (i≢j : ¬ i ≡ j) (i≢k : ¬ i ≡ k)
  → punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-inj {_} {i} {j} {k} i≢j i≢k p with fsplit i | fsplit j | fsplit k
punchOut-inj {zero} {i} {j} {k} i≢j i≢k p | _ | _ | _ =
  Empty.elim (i≢j (i ≡⟨ sym (isContrFin1 .snd i) ⟩ c ≡⟨ isContrFin1 .snd j ⟩ j ∎))
    where c = isContrFin1 .fst
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | inl prfj | _ =
  Empty.elim (i≢j (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfj ⟩ j ∎))
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | _ | inl prfk =
  Empty.elim (i≢k (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfk ⟩ k ∎))
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | inr (kj , prfj) | inr (kk , prfk) =
  j       ≡⟨ sym prfj ⟩
  fsuc kj ≡⟨ cong fsuc p ⟩
  fsuc kk ≡⟨ prfk ⟩
  k       ∎
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inl prfj | inl prfk =
  j     ≡⟨ sym prfj ⟩
  fzero ≡⟨ prfk ⟩
  k     ∎
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inr (kj , prfj) | inr (kk , prfk) =
  j ≡⟨ sym prfj ⟩
  fsuc kj ≡⟨ cong fsuc lemma4 ⟩
  fsuc kk ≡⟨ prfk ⟩
  k ∎
  where
    lemma1 = λ q → i≢j (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kj ≡⟨ prfj ⟩ j ∎)
    lemma2 = λ q → i≢k (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kk ≡⟨ prfk ⟩ k ∎)
    lemma3 = fsuc-inj p
    lemma4 = punchOut-inj lemma1 lemma2 lemma3
punchOut-inj {suc m} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inl prfj | inr (kk , prfk) =
  Empty.rec (fznotfs p)
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inr (kj , prfj) | inl prfk =
  Empty.rec (fznotfs (sym p))

pigeonhole-special
  : ∀ {n}
  → (f : Fin (suc n) → Fin n)
  → Σ[ i ∈ Fin (suc n) ] Σ[ j ∈ Fin (suc n) ] (¬ i ≡ j) × (f i ≡ f j)
pigeonhole-special {zero} f = Empty.rec (¬Fin0 (f fzero))
pigeonhole-special {suc n} f =
  proof (any?
    (λ (i : Fin (suc n)) →
      discreteFin (f (inject< ≤-refl i)) (f (suc n , ≤-refl))
    ))
  where
    proof
      : Dec (Σ (Fin (suc n)) (λ z → f (inject< ≤-refl z) ≡ f (suc n , ≤-refl)))
      → Σ[ i ∈ Fin (suc (suc n)) ] Σ[ j ∈ Fin (suc (suc n)) ] (¬ i ≡ j) × (f i ≡ f j)
    proof (yes (i , prf)) = inject< ≤-refl i , (suc n , ≤-refl) , inject<-ne i , prf
    proof (no h) =
      let
        g : Fin (suc n) → Fin n
        g k = punchOut
          {i = f (suc n , ≤-refl)}
          {j = f (inject< ≤-refl k)}
          (λ p → h (k , Fin-fst-≡ (sym (cong fst p))))
        i , j , i≢j , p = pigeonhole-special g
      in
        inject< ≤-refl i
      , inject< ≤-refl j
      , (λ q → i≢j (Fin-fst-≡ (cong fst q)))
      , punchOut-inj
          {i = f (suc n , ≤-refl)}
          {j = f (inject< ≤-refl i)}
          {k = f (inject< ≤-refl j)}
          (λ q → h (i , Fin-fst-≡ (sym (cong fst q))))
          (λ q → h (j , Fin-fst-≡ (sym (cong fst q))))
          (Fin-fst-≡ (cong fst p))

pigeonhole
  : ∀ {m n}
  → m < n
  → (f : Fin n → Fin m)
  → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j)
pigeonhole {m} {n} (zero , sm≡n) f =
  transport transport-prf (pigeonhole-special f′)
  where
    f′ : Fin (suc m) → Fin m
    f′ = subst (λ h → Fin h → Fin m) (sym sm≡n) f

    f′≡f : PathP (λ i → Fin (sm≡n i) → Fin m) f′ f
    f′≡f i = transport-fillerExt (cong (λ h → Fin h → Fin m) (sym sm≡n)) (~ i) f

    transport-prf
      : (Σ[ i ∈ Fin (suc m) ] Σ[ j ∈ Fin (suc m) ] (¬ i ≡ j) × (f′ i ≡ f′ j))
      ≡ (Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j))
    transport-prf φ =
      Σ[ i ∈ Fin (sm≡n φ) ] Σ[ j ∈ Fin (sm≡n φ) ]
        (¬ i ≡ j) × (f′≡f φ i ≡ f′≡f φ j)
pigeonhole {m} {n} (suc k , prf) f =
  let
    g : Fin (suc n′) → Fin n′
    g k = fst (f′ k) , <-trans (snd (f′ k)) m<n′
    i , j , ¬q , r = pigeonhole-special g
  in transport transport-prf (i , j , ¬q , Σ≡Prop (λ _ → m≤n-isProp) (cong fst r))
  where
    n′ : ℕ
    n′ = k + suc m

    n≡sn′ : n ≡ suc n′
    n≡sn′ =
      n ≡⟨ sym prf ⟩
      suc (k + suc m) ≡⟨ refl ⟩
      suc n′ ∎

    m<n′ : m < n′
    m<n′ = k , injSuc (suc (k + suc m) ≡⟨ prf ⟩ n ≡⟨ n≡sn′ ⟩ suc n′ ∎)

    f′ : Fin (suc n′) → Fin m
    f′ = subst (λ h → Fin h → Fin m) n≡sn′ f

    f′≡f : PathP (λ i → Fin (n≡sn′ (~ i)) → Fin m) f′ f
    f′≡f i = transport-fillerExt (cong (λ h → Fin h → Fin m) n≡sn′) (~ i) f

    transport-prf
      : (Σ[ i ∈ Fin (suc n′) ] Σ[ j ∈ Fin (suc n′) ] (¬ i ≡ j) × (f′ i ≡ f′ j))
      ≡ (Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j))
    transport-prf φ =
      Σ[ i ∈ Fin (n≡sn′ (~ φ)) ] Σ[ j ∈ Fin (n≡sn′ (~ φ)) ]
        (¬ i ≡ j) × (f′≡f φ i ≡ f′≡f φ j)

Fin-inj′ : {n m : ℕ} → n < m → ¬ Fin m ≡ Fin n
Fin-inj′ n<m p =
  let
    i , j , i≢j , q = pigeonhole n<m (transport p)
  in i≢j (
    i ≡⟨ refl ⟩
    fst (pigeonhole n<m (transport p)) ≡⟨ transport-p-inj {p = p} q ⟩
    fst (snd (pigeonhole n<m (transport p))) ≡⟨ refl ⟩
    j ∎
  )
  where
    transport-p-inj
      : ∀ {A B : Type ℓ} {x y : A} {p : A ≡ B}
      → transport p x ≡ transport p y
      → x ≡ y
    transport-p-inj {x = x} {y = y} {p = p} q =
      x ≡⟨ sym (transport⁻Transport p x) ⟩
      transport (sym p) (transport p x) ≡⟨ cong (transport (sym p)) q ⟩
      transport (sym p) (transport p y) ≡⟨ transport⁻Transport p y ⟩
      y ∎

Fin-inj : (n m : ℕ) → Fin n ≡ Fin m → n ≡ m
Fin-inj n m p with n ≟ m
... | eq prf = prf
... | lt n<m = Empty.rec (Fin-inj′ n<m (sym p))
... | gt n>m = Empty.rec (Fin-inj′ n>m p)

≤-*sk-cancel : ∀ {m} {k} {n} → m * suc k ≤ n * suc k → m ≤ n
≤-*sk-cancel {m} {k} {n} (d , p) = o , inj-*sm {m = k} goal where
  r = d % suc k
  o = d / suc k
  resn*k : Residue (suc k) (n * suc k)
  resn*k = ((r , n%sk<sk d k) , (o + m)) , reason where
   reason = expand× ((r , n%sk<sk d k) , o + m) ≡⟨ expand≡ (suc k) r (o + m) ⟩
            (o + m) * suc k + r                 ≡[ i ]⟨ +-comm (*-distribʳ o m (suc k) (~ i)) r i ⟩
            r + (o * suc k + m * suc k)         ≡⟨ +-assoc r (o * suc k) (m * suc k) ⟩
            (r + o * suc k) + m * suc k         ≡⟨ cong (_+ m * suc k) (+-comm r (o * suc k) ∙ moddiv d (suc k)) ⟩
            d + m * suc k                       ≡⟨ p ⟩
            n * suc k ∎

  residuek*n : ∀ k n → (r : Residue (suc k) (n * suc k)) → ((fzero , n) , expand≡ (suc k) 0 n ∙ +-zero _) ≡ r
  residuek*n _ _ = isContr→isProp isContrResidue _

  r≡0 : r ≡ 0
  r≡0 = cong (toℕ ∘ extract) (sym (residuek*n k n resn*k))
  d≡o*sk : d ≡ o * suc k
  d≡o*sk = sym (moddiv d (suc k)) ∙∙ cong (o * suc k +_) r≡0 ∙∙ +-zero _
  goal : (o + m) * suc k ≡ n * suc k
  goal = sym (*-distribʳ o m (suc k)) ∙∙ cong (_+ m * suc k) (sym d≡o*sk) ∙∙ p

<-*sk-cancel : ∀ {m} {k} {n} → m * suc k < n * suc k → m < n
<-*sk-cancel {m} {k} {n} p = goal where
  ≤-helper : m ≤ n
  ≤-helper = ≤-*sk-cancel (pred-≤-pred (<≤-trans p (≤-suc ≤-refl)))
  goal : m < n
  goal = case <-split (suc-≤-suc ≤-helper) of λ
    { (inl g) → g
    ; (inr e) → Empty.rec (¬m<m (subst (λ m → m * suc k < n * suc k) e p))
    }

factorEquiv : ∀ {n} {m} → Fin n × Fin m ≃ Fin (n * m)
factorEquiv {zero} {m} = uninhabEquiv (¬Fin0 ∘ fst) ¬Fin0
factorEquiv {suc n} {m} = intro , isEmbedding×isSurjection→isEquiv (isEmbeddingIntro , isSurjectionIntro) where
  intro : Fin (suc n) × Fin m → Fin (suc n * m)
  intro (nn , mm) = nm , subst (λ nm₁ → nm₁ < suc n * m) (sym (expand≡ _ (toℕ nn) (toℕ mm))) nm<n*m where
    nm : ℕ
    nm = expand× (nn , toℕ mm)
    nm<n*m : toℕ mm * suc n + toℕ nn < suc n * m
    nm<n*m =
      toℕ mm * suc n + toℕ nn <≤⟨ <-k+ (snd nn) ⟩
      toℕ mm * suc n + suc n  ≡≤⟨ +-comm _ (suc n) ⟩
      suc (toℕ mm) * suc n    ≤≡⟨ ≤-*k (snd mm) ⟩
      m * suc n               ≡⟨ *-comm _ (suc n) ⟩
      suc n * m               ∎ where open <-Reasoning

  intro-injective : ∀ {o} {p} → intro o ≡ intro p → o ≡ p
  intro-injective {o} {p} io≡ip = λ i → io′≡ip′ i .fst , toℕ-injective {fj = snd o} {fk = snd p} (cong snd io′≡ip′) i where
    io′≡ip′ : (fst o , toℕ (snd o)) ≡ (fst p , toℕ (snd p))
    io′≡ip′ = expand×Inj _ (cong fst io≡ip)
  isEmbeddingIntro : isEmbedding intro
  isEmbeddingIntro = injEmbedding (isSet× isSetFin isSetFin) isSetFin intro-injective

  elimF : ∀ nm → fiber intro nm
  elimF nm = ((nn , nn<n) , (mm , mm<m)) , toℕ-injective (reduce n (toℕ nm) .snd) where
    mm = toℕ nm / suc n
    nn = toℕ nm % suc n

    nmmoddiv : mm * suc n + nn ≡ toℕ nm
    nmmoddiv = moddiv _ (suc n)
    nn<n : nn < suc n
    nn<n = n%sk<sk (toℕ nm) _

    nmsnd : mm * suc n + nn < suc n * m
    nmsnd = subst (λ l → l < suc n * m) (sym nmmoddiv) (snd nm)
    mm*sn<m*sn : mm * suc n < m * suc n
    mm*sn<m*sn =
      mm * suc n      ≤<⟨ nn , +-comm nn (mm * suc n) ⟩
      mm * suc n + nn <≡⟨ nmsnd ⟩
      suc n * m       ≡⟨ *-comm (suc n) m ⟩
      m * suc n       ∎ where open <-Reasoning
    mm<m : mm < m
    mm<m = <-*sk-cancel mm*sn<m*sn

  isSurjectionIntro : isSurjection intro
  isSurjectionIntro = ∣_∣ ∘ elimF
