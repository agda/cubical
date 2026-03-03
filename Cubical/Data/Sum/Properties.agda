module Cubical.Data.Sum.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding

open import Cubical.Data.Sum.Base as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open Iso


private
  variable
    ℓa ℓb ℓc ℓd ℓe : Level
    A : Type ℓa
    B : Type ℓb
    C : Type ℓc
    D : Type ℓd
    E : A ⊎ B → Type ℓe


-- Path space of sum type
module ⊎Path {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  Cover : A ⊎ B → A ⊎ B → Type (ℓ-max ℓ ℓ')
  Cover (inl a) (inl a') = Lift ℓ' (a ≡ a')
  Cover (inl _) (inr _) = ⊥*
  Cover (inr _) (inl _) = ⊥*
  Cover (inr b) (inr b') = Lift ℓ (b ≡ b')

  reflCode : (c : A ⊎ B) → Cover c c
  reflCode (inl a) = lift refl
  reflCode (inr b) = lift refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode (inl a) (inl a') (lift p) = cong inl p
  decode (inl a) (inr b') ()
  decode (inr b) (inl a') ()
  decode (inr b) (inr b') (lift q) = cong inr q

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl (inl a) = refl
  decodeRefl (inr b) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode (inl a) (inl _) (lift d) =
    J (λ a' p → encode (inl a) (inl a') (cong inl p) ≡ lift p) (encodeRefl (inl a)) d
  encodeDecode (inr a) (inr _) (lift d) =
    J (λ a' p → encode (inr a) (inr a') (cong inr p) ≡ lift p) (encodeRefl (inr a)) d

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' =
    isoToEquiv (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → isOfHLevel (suc (suc n)) B
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p q (inl a) (inl a') = isOfHLevelLift (suc n) (p a a')
  isOfHLevelCover n p q (inl a) (inr b') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inl a') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inr b') = isOfHLevelLift (suc n) (q b b')

isEmbedding-inl : isEmbedding (inl {A = A} {B = B})
isEmbedding-inl w z = snd (compEquiv LiftEquiv (⊎Path.Cover≃Path (inl w) (inl z)))

isEmbedding-inr : isEmbedding (inr {A = A} {B = B})
isEmbedding-inr w z = snd (compEquiv LiftEquiv (⊎Path.Cover≃Path (inr w) (inr z)))

isOfHLevel⊎ : (n : HLevel)
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) B
  → isOfHLevel (suc (suc n)) (A ⊎ B)
isOfHLevel⊎ n lA lB c c' =
  isOfHLevelRetract (suc n)
    (⊎Path.encode c c')
    (⊎Path.decode c c')
    (⊎Path.decodeEncode c c')
    (⊎Path.isOfHLevelCover n lA lB c c')

isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ propA _ _ (inl x) (inl y) i = inl (propA x y i)
isProp⊎ _ _ AB⊥ (inl x) (inr y) = ⊥.rec (AB⊥ x y)
isProp⊎ _ _ AB⊥ (inr x) (inl y) = ⊥.rec (AB⊥ y x)
isProp⊎ _ propB _ (inr x) (inr y) i = inr (propB x y i)

isSet⊎ : isSet A → isSet B → isSet (A ⊎ B)
isSet⊎ = isOfHLevel⊎ 0

isGroupoid⊎ : isGroupoid A → isGroupoid B → isGroupoid (A ⊎ B)
isGroupoid⊎ = isOfHLevel⊎ 1

is2Groupoid⊎ : is2Groupoid A → is2Groupoid B → is2Groupoid (A ⊎ B)
is2Groupoid⊎ = isOfHLevel⊎ 2

discrete⊎ : Discrete A → Discrete B → Discrete (A ⊎ B)
discrete⊎ decA decB (inl a) (inl a') =
  mapDec (cong inl) (λ p q → p (isEmbedding→Inj isEmbedding-inl _ _ q)) (decA a a')
discrete⊎ decA decB (inl a) (inr b') = no (λ p → lower (⊎Path.encode (inl a) (inr b') p))
discrete⊎ decA decB (inr b) (inl a') = no ((λ p → lower (⊎Path.encode (inr b) (inl a') p)))
discrete⊎ decA decB (inr b) (inr b') =
  mapDec (cong inr) (λ p q → p (isEmbedding→Inj isEmbedding-inr _ _ q)) (decB b b')

⊎Iso : Iso A C → Iso B D → Iso (A ⊎ B) (C ⊎ D)
fun (⊎Iso iac ibd) (inl x) = inl (iac .fun x)
fun (⊎Iso iac ibd) (inr x) = inr (ibd .fun x)
inv (⊎Iso iac ibd) (inl x) = inl (iac .inv x)
inv (⊎Iso iac ibd) (inr x) = inr (ibd .inv x)
sec (⊎Iso iac ibd) (inl x) = cong inl (iac .sec x)
sec (⊎Iso iac ibd) (inr x) = cong inr (ibd .sec x)
ret (⊎Iso iac ibd) (inl x)  = cong inl (iac .ret x)
ret (⊎Iso iac ibd) (inr x)  = cong inr (ibd .ret x)

⊎-equiv : A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
⊎-equiv p q = isoToEquiv (⊎Iso (equivToIso p) (equivToIso q))

⊎-swap-Iso : Iso (A ⊎ B) (B ⊎ A)
fun ⊎-swap-Iso (inl x) = inr x
fun ⊎-swap-Iso (inr x) = inl x
inv ⊎-swap-Iso (inl x) = inr x
inv ⊎-swap-Iso (inr x) = inl x
sec ⊎-swap-Iso (inl _) = refl
sec ⊎-swap-Iso (inr _) = refl
ret ⊎-swap-Iso (inl _)  = refl
ret ⊎-swap-Iso (inr _)  = refl

⊎-swap-≃ : A ⊎ B ≃ B ⊎ A
⊎-swap-≃ = isoToEquiv ⊎-swap-Iso

⊎-assoc-Iso : Iso ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
fun ⊎-assoc-Iso (inl (inl x)) = inl x
fun ⊎-assoc-Iso (inl (inr x)) = inr (inl x)
fun ⊎-assoc-Iso (inr x)       = inr (inr x)
inv ⊎-assoc-Iso (inl x)       = inl (inl x)
inv ⊎-assoc-Iso (inr (inl x)) = inl (inr x)
inv ⊎-assoc-Iso (inr (inr x)) = inr x
sec ⊎-assoc-Iso (inl _)       = refl
sec ⊎-assoc-Iso (inr (inl _)) = refl
sec ⊎-assoc-Iso (inr (inr _)) = refl
ret ⊎-assoc-Iso (inl (inl _))  = refl
ret ⊎-assoc-Iso (inl (inr _))  = refl
ret ⊎-assoc-Iso (inr _)        = refl

⊎-assoc-≃ : (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc-≃ = isoToEquiv ⊎-assoc-Iso

⊎-IdR-⊥-Iso : Iso (A ⊎ ⊥) A
fun ⊎-IdR-⊥-Iso (inl x) = x
inv ⊎-IdR-⊥-Iso x       = inl x
sec ⊎-IdR-⊥-Iso _      = refl
ret ⊎-IdR-⊥-Iso (inl _) = refl

⊎-IdL-⊥-Iso : Iso (⊥ ⊎ A) A
fun ⊎-IdL-⊥-Iso (inr x) = x
inv ⊎-IdL-⊥-Iso x       = inr x
sec ⊎-IdL-⊥-Iso _      = refl
ret ⊎-IdL-⊥-Iso (inr _) = refl

⊎-IdL-⊥*-Iso : ∀ {ℓ} → Iso (⊥* {ℓ} ⊎ A) A
fun ⊎-IdL-⊥*-Iso (inr x) = x
inv ⊎-IdL-⊥*-Iso x       = inr x
sec ⊎-IdL-⊥*-Iso _      = refl
ret ⊎-IdL-⊥*-Iso (inr _) = refl

⊎-IdR-⊥*-Iso : ∀ {ℓ} → Iso (A ⊎ ⊥* {ℓ}) A
fun ⊎-IdR-⊥*-Iso (inl x) = x
inv ⊎-IdR-⊥*-Iso x       = inl x
sec ⊎-IdR-⊥*-Iso _      = refl
ret ⊎-IdR-⊥*-Iso (inl _) = refl

⊎-IdR-⊥-≃ : A ⊎ ⊥ ≃ A
⊎-IdR-⊥-≃ = isoToEquiv ⊎-IdR-⊥-Iso

⊎-IdL-⊥-≃ : ⊥ ⊎ A ≃ A
⊎-IdL-⊥-≃ = isoToEquiv ⊎-IdL-⊥-Iso

⊎-IdR-⊥*-≃ : ∀ {ℓ} → A ⊎ ⊥* {ℓ} ≃ A
⊎-IdR-⊥*-≃ = isoToEquiv ⊎-IdR-⊥*-Iso

⊎-IdL-⊥*-≃ : ∀ {ℓ} → ⊥* {ℓ} ⊎ A ≃ A
⊎-IdL-⊥*-≃ = isoToEquiv ⊎-IdL-⊥*-Iso

Π⊎Iso : Iso ((x : A ⊎ B) → E x) (((a : A) → E (inl a)) × ((b : B) → E (inr b)))
fun Π⊎Iso f .fst a = f (inl a)
fun Π⊎Iso f .snd b = f (inr b)
inv Π⊎Iso (g1 , g2) (inl a) = g1 a
inv Π⊎Iso (g1 , g2) (inr b) = g2 b
sec Π⊎Iso (g1 , g2) i .fst a = g1 a
sec Π⊎Iso (g1 , g2) i .snd b = g2 b
ret Π⊎Iso f i (inl a) = f (inl a)
ret Π⊎Iso f i (inr b) = f (inr b)

Σ⊎Iso : Iso (Σ (A ⊎ B) E) ((Σ A (λ a → E (inl a))) ⊎ (Σ B (λ b → E (inr b))))
fun Σ⊎Iso (inl a , ea) = inl (a , ea)
fun Σ⊎Iso (inr b , eb) = inr (b , eb)
inv Σ⊎Iso (inl (a , ea)) = (inl a , ea)
inv Σ⊎Iso (inr (b , eb)) = (inr b , eb)
sec Σ⊎Iso (inl (a , ea)) = refl
sec Σ⊎Iso (inr (b , eb)) = refl
ret Σ⊎Iso (inl a , ea) = refl
ret Σ⊎Iso (inr b , eb) = refl

×DistR⊎Iso : Iso (A × (B ⊎ C)) ((A × B) ⊎ (A × C))
fun ×DistR⊎Iso (a , inl b) = inl (a , b)
fun ×DistR⊎Iso (a , inr c) = inr (a , c)
inv ×DistR⊎Iso (inl (a , b)) = a , inl b
inv ×DistR⊎Iso (inr (a , c)) = a , inr c
sec ×DistR⊎Iso (inl (a , b)) = refl
sec ×DistR⊎Iso (inr (a , c)) = refl
ret ×DistR⊎Iso (a , inl b) = refl
ret ×DistR⊎Iso (a , inr c) = refl

Π⊎≃ : ((x : A ⊎ B) → E x) ≃ ((a : A) → E (inl a)) × ((b : B) → E (inr b))
Π⊎≃ = isoToEquiv Π⊎Iso

Σ⊎≃ : (Σ (A ⊎ B) E) ≃ ((Σ A (λ a → E (inl a))) ⊎ (Σ B (λ b → E (inr b))))
Σ⊎≃ = isoToEquiv Σ⊎Iso

⊎Monotone↪ : A ↪ C → B ↪ D → (A ⊎ B) ↪ (C ⊎ D)
⊎Monotone↪ (f , embf) (g , embg) = (map f g) , emb
  where coverToMap : ∀ x y → ⊎Path.Cover x y
                           → ⊎Path.Cover (map f g x) (map f g y)
        coverToMap (inl _) (inl _) cover = lift (cong f (lower cover))
        coverToMap (inr _) (inr _) cover = lift (cong g (lower cover))

        equiv : ∀ x y → isEquiv (coverToMap x y)
        equiv (inl a₀) (inl a₁)
          = ((invEquiv LiftEquiv)
            ∙ₑ ((cong f) , (embf a₀ a₁))
            ∙ₑ LiftEquiv) .snd
        equiv (inl a₀) (inr b₁) .equiv-proof ()
        equiv (inr b₀) (inl a₁) .equiv-proof ()
        equiv (inr b₀) (inr b₁)
          = ((invEquiv LiftEquiv)
            ∙ₑ ((cong g) , (embg b₀ b₁))
            ∙ₑ LiftEquiv) .snd

        lemma : ∀ x y
              → ∀ (p : x ≡ y)
              → cong (map f g) p ≡
                     ⊎Path.decode
                       (map f g x)
                       (map f g y)
                       (coverToMap x y (⊎Path.encode x y p))
        lemma (inl a₀) _
          = J (λ y p
              → cong (map f g) p ≡
                     ⊎Path.decode (map f g (inl a₀))
                                  (map f g y)
                                  (coverToMap (inl a₀) y
                                              (⊎Path.encode (inl a₀) y p)))
            (sym $ cong (cong inl) (cong (cong f) (transportRefl _)))
        lemma (inr b₀) _
          = J (λ y p
              → cong (map f g) p ≡
                     ⊎Path.decode
                       (map f g (inr b₀))
                       (map f g y)
                       (coverToMap (inr b₀) y (⊎Path.encode (inr b₀) y p)))
              (sym $ cong (cong inr) (cong (cong g) (transportRefl _)))

        emb : isEmbedding (map f g)
        emb x y = subst (λ eq → isEquiv eq)
                        (sym (funExt (lemma x y)))
                          ((x ≡ y         ≃⟨ invEquiv (⊎Path.Cover≃Path x y) ⟩
                          ⊎Path.Cover x y ≃⟨ (coverToMap x y) , (equiv x y) ⟩
                          ⊎Path.Cover
                            (map f g x)
                            (map f g y)   ≃⟨ ⊎Path.Cover≃Path
                                             (map f g x)
                                             (map f g y) ⟩
                          map f g x ≡ map f g y ■) .snd)

-- A ⊎ B ≃ C ⊎ D implies B ≃ D if the first equiv respects inl
Iso⊎→Iso : (f : Iso A C) (e : Iso (A ⊎ B) (C ⊎ D))
   → ((a : A) → Iso.fun e (inl a) ≡ inl (Iso.fun f a))
   → Iso B D
Iso⊎→Iso {A = A} {C = C} {B = B} {D = D} f e p = Iso'
  where
  ⊥-fib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Type
  ⊥-fib (inl x) = ⊥
  ⊥-fib (inr x) = Unit

  module _ {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {D : Type ℓd}
         (f : Iso A C)
         (e : Iso (A ⊎ B) (C ⊎ D))
         (p : (a : A) → Iso.fun e (inl a) ≡ inl (Iso.fun f a)) where
    T : (b : B) → Type _
    T b = Σ[ d' ∈ C ⊎ D ] (Iso.fun e (inr b) ≡ d')

    T-elim : ∀ {ℓ} (b : B) {P : (x : T b) → Type ℓ}
           → ((d : D) (s : _) → P (inr d , s))
           → (x : _) → P x
    T-elim b ind (inl x , q) =
      ⊥.rec (subst ⊥-fib (sym (sym (Iso.ret e _)
          ∙ cong (Iso.inv e)
             (p _ ∙ cong inl (Iso.sec f x) ∙ sym q)
          ∙ Iso.ret e _)) tt)
    T-elim b ind (inr x , y) = ind x y

  e-pres-inr-help : (b : B) → T f e p b  → D
  e-pres-inr-help b = T-elim f e p b λ d _ → d

  p' : (a : C) → Iso.inv e (inl a) ≡ inl (Iso.inv f a)
  p' c = cong (Iso.inv e ∘ inl) (sym (Iso.sec f c))
      ∙∙ cong (Iso.inv e) (sym (p (Iso.inv f c)))
      ∙∙ Iso.ret e _

  e⁻-pres-inr-help : (d : D) → T (invIso f) (invIso e) p' d → B
  e⁻-pres-inr-help d = T-elim (invIso f) (invIso e) p' d λ b _ → b

  e-pres-inr : B → D
  e-pres-inr b = e-pres-inr-help b (_ , refl)

  e⁻-pres-inr : D → B
  e⁻-pres-inr d = e⁻-pres-inr-help d (_ , refl)

  lem1 : (b : B) (e : T f e p b) (d : _)
    → e⁻-pres-inr-help (e-pres-inr-help b e) d ≡ b
  lem1 b = T-elim f e p b λ d s
    → T-elim (invIso f) (invIso e) p' _
      λ b' s' → invEq (_ , isEmbedding-inr _ _)
        (sym s' ∙ cong (Iso.inv e) (sym s) ∙ Iso.ret e _)

  lem2 : (d : D) (e : T (invIso f) (invIso e) p' d ) (t : _)
    → e-pres-inr-help (e⁻-pres-inr-help d e) t ≡ d
  lem2 d = T-elim (invIso f) (invIso e) p' d
    λ b s → T-elim f e p _ λ d' s'
    → invEq (_ , isEmbedding-inr _ _)
         (sym s' ∙ cong (Iso.fun e) (sym s) ∙ Iso.sec e _)

  Iso' : Iso B D
  Iso.fun Iso' = e-pres-inr
  Iso.inv Iso' = e⁻-pres-inr
  Iso.sec Iso' x = lem2 x (_ , refl) (_ , refl)
  Iso.ret Iso' x = lem1 x (_ , refl) (_ , refl)

Lift⊎Iso : ∀ (ℓ : Level)
  → Iso (Lift ℓ A ⊎ Lift ℓ B)
         (Lift ℓ (A ⊎ B))
fun (Lift⊎Iso ℓD) (inl x) = liftFun inl x
fun (Lift⊎Iso ℓD) (inr x) = liftFun inr x
inv (Lift⊎Iso ℓD) (lift (inl x)) = inl (lift x)
inv (Lift⊎Iso ℓD) (lift (inr x)) = inr (lift x)
sec (Lift⊎Iso ℓD) (lift (inl x)) = refl
sec (Lift⊎Iso ℓD) (lift (inr x)) = refl
ret (Lift⊎Iso ℓD) (inl x) = refl
ret (Lift⊎Iso ℓD) (inr x) = refl
