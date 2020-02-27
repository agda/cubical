{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Structure.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.Univalence renaming (ua-pathToEquiv to ua-pathToEquiv')
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

open import Cubical.Foundations.Structure.Base
open import Cubical.Foundations.Structure.SNS renaming (SNS₄ to SNS)

-- For technical reasons we reprove ua-pathToEquiv using the
-- particular proof constructed by iso→HAEquiv. The reason is that we
-- want to later be able to extract
--
--   eq : ua-au (ua e) ≡ cong ua (au-ua e)
--
uaHAEquiv : ∀ {ℓ} (A B : Type ℓ) → HAEquiv (A ≃ B) (A ≡ B)
uaHAEquiv A B = iso→HAEquiv (iso ua pathToEquiv ua-pathToEquiv' pathToEquiv-ua)
open isHAEquiv

-- We now extract the particular proof constructed from iso→HAEquiv
-- for reasons explained above.
ua-pathToEquiv : ∀ {ℓ} {A B : Type ℓ} (e : A ≡ B) → ua (pathToEquiv e) ≡ e
ua-pathToEquiv e = uaHAEquiv _ _ .snd .ret e

private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'

-- We can now directly define a function
--    sip : A ≃[ ι ] B → A ≡ B
-- together with is inverse.
-- Here, these functions use SNS and are expressed using a Σ-type instead as it is a bit
-- easier to work with
sip : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
    → (A B : TypeWithStr ℓ S)
    → A ≃[ ι ] B
    → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
sip S ι θ A B (e , p) = ua e , invEq (θ A B e) p

-- The inverse to sip using the following little lemma

private
  lem : (S : Type ℓ → Type ℓ') (A B : TypeWithStr ℓ S) (e : typ A ≡ typ B)
      → PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd) ≡
        PathP (λ i → S (e i)) (A .snd) (B .snd)
  lem S A B e i = PathP (λ j → S (ua-pathToEquiv e i j)) (A .snd) (B .snd)

sip⁻ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
     → (A B : TypeWithStr ℓ S)
     → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
     → A ≃[ ι ] B
sip⁻ S ι θ A B (e , r) = pathToEquiv e , θ A B (pathToEquiv e) .fst q
  where
  q : PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd)
  q = transport (λ i → lem S A B e (~ i)) r


-- we can rather directly show that sip and sip⁻ are mutually inverse:
sip-sip⁻ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
         → (A B : TypeWithStr ℓ S)
         → (r : Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B)))
         → sip S ι θ A B (sip⁻ S ι θ A B r) ≡ r
sip-sip⁻ S ι θ A B (p , q) =
    sip S ι θ A B (sip⁻ S ι θ A B (p , q))
  ≡⟨ refl ⟩
    ua (pathToEquiv p) , invEq (θ A B (pathToEquiv p)) (θ A B (pathToEquiv p) .fst (transport (λ i → lem S A B p (~ i)) q))
  ≡⟨ (λ i → ua (pathToEquiv p) , secEq (θ A B (pathToEquiv p)) (transport (λ i → lem S A B p (~ i)) q) i) ⟩
    ua (pathToEquiv p) , transport (λ i → lem S A B p (~ i)) q
  ≡⟨ (λ i → ua-pathToEquiv p i ,
            transp (λ k → PathP (λ j → S (ua-pathToEquiv p (i ∧ k) j)) (str A) (str B))
                   (~ i)
                   (transport (λ i → lem S A B p (~ i)) q)) ⟩
    p , transport (λ i → lem S A B p i) (transport (λ i → lem S A B p (~ i)) q)
  ≡⟨ (λ i → p , transportTransport⁻ (lem S A B p) q i) ⟩
    p , q ∎


-- The trickier direction:
sip⁻-sip : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
         → (A B : TypeWithStr ℓ S)
         → (r : A ≃[ ι ] B)
         → sip⁻ S ι θ A B (sip S ι θ A B r) ≡ r
sip⁻-sip S ι θ A B (e , p) =
    sip⁻ S ι θ A B (sip S ι θ A B (e , p))
  ≡⟨ refl ⟩
    pathToEquiv (ua e) , θ A B (pathToEquiv (ua e)) .fst (f⁺ p')
  ≡⟨ (λ i → pathToEquiv-ua e i , θ A B (pathToEquiv-ua e i) .fst (pth' i)) ⟩
    e , θ A B e .fst (f⁻ (f⁺ p'))
  ≡⟨ (λ i → e , θ A B e .fst (transportTransport⁻ (lem S A B (ua e)) p' i)) ⟩
    e , θ A B e .fst (invEq (θ A B e) p)
  ≡⟨ (λ i → e , (retEq (θ A B e) p i)) ⟩
    e , p ∎
  where
  p' : PathP (λ i → S (ua e i)) (str A) (str B)
  p' = invEq (θ A B e) p

  f⁺ : PathP (λ i → S (ua e i)) (str A) (str B)
     → PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (str A) (str B)
  f⁺ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) (~ i) j)) (str A) (str B))

  f⁻ : PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (str A) (str B)
     → PathP (λ i → S (ua e i)) (str A) (str B)
  f⁻ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) i j)) (str A) (str B))

  -- We can prove the following as in sip∘pis-id, but the type is not
  -- what we want as it should be "cong ua (pathToEquiv-ua e)"
  pth : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (str A) (str B))
              (f⁺ p') (f⁻ (f⁺ p'))
  pth i = transp (λ k → PathP (λ j → S (ua-pathToEquiv (ua e) (i ∧ k) j)) (str A) (str B))
                 (~ i)
                 (f⁺ p')

  -- So we build an equality that we want to cast the types with
  casteq : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (str A) (str B))
                 (f⁺ p') (f⁻ (f⁺ p'))
         ≡ PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (str A) (str B))
                 (f⁺ p') (f⁻ (f⁺ p'))
  casteq i = PathP (λ j → PathP (λ k → S (eq i j k)) (str A) (str B)) (f⁺ p') (f⁻ (f⁺ p'))
    where
    -- This is where we need the half-adjoint equivalence property
    eq : ua-pathToEquiv (ua e) ≡ cong ua (pathToEquiv-ua e)
    eq = sym (uaHAEquiv (typ A) (typ B) .snd .com e)

  -- We then get a term of the type we need
  pth' : PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (str A) (str B))
               (f⁺ p') (f⁻ (f⁺ p'))
  pth' = transport (λ i → casteq i) pth


-- Finally package everything up to get the cubical SIP
SIP : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
    → (A B : TypeWithStr ℓ S)
    → A ≃[ ι ] B ≃ (A ≡ B)
SIP S ι θ A B = (A ≃[ ι ] B ) ≃⟨ eq ⟩ Σ≡
  where
  eq : A ≃[ ι ] B ≃ Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
  eq = isoToEquiv (iso (sip S ι θ A B) (sip⁻ S ι θ A B)
                       (sip-sip⁻ S ι θ A B) (sip⁻-sip S ι θ A B))
