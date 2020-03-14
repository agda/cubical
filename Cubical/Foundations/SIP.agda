{-

In this file we apply the cubical machinery to Martin Hötzel-Escardó's
structure identity principle:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence renaming (ua-pathToEquiv to ua-pathToEquiv')
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties renaming (cong≃ to _⋆_)
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.Structure public

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    S : Type ℓ₁ → Type ℓ₂

-- For technical reasons we reprove ua-pathToEquiv using the
-- particular proof constructed by iso→HAEquiv. The reason is that we
-- want to later be able to extract
--
--   eq : ua-au (ua e) ≡ cong ua (au-ua e)
--
uaHAEquiv : (A B : Type ℓ₁) → HAEquiv (A ≃ B) (A ≡ B)
uaHAEquiv A B = iso→HAEquiv (iso ua pathToEquiv ua-pathToEquiv' pathToEquiv-ua)
open isHAEquiv

-- We now extract the particular proof constructed from iso→HAEquiv
-- for reasons explained above.
ua-pathToEquiv : {A B : Type ℓ₁} (e : A ≡ B) → ua (pathToEquiv e) ≡ e
ua-pathToEquiv e = uaHAEquiv _ _ .snd .ret e


-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
SNS-≡ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
SNS-≡ {ℓ₁} S ι = ∀ {X : Type ℓ₁} (s t : S X) → ι (X , s) (X , t) (idEquiv X) ≃ (s ≡ t)


-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : (A : TypeWithStr ℓ₁ S) (ι : StrIso S ℓ₂) (B : TypeWithStr ℓ₁ S) → Type (ℓ-max ℓ₁ ℓ₂)
A ≃[ ι ] B = Σ[ e ∈ typ A ≃ typ B ] (ι A B e)



-- The following PathP version of SNS-≡ is a bit easier to
-- work with for the proof of the SIP
SNS-PathP : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
SNS-PathP {ℓ₁} S ι = {A B : TypeWithStr ℓ₁ S} (e : typ A ≃ typ B)
                  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction SNS-≡→SNS-PathP corresponds more or less to a
-- dependent EquivJ formulation of Escardó's homomorphism-lemma.
SNS-PathP→SNS-≡ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → SNS-PathP S ι → SNS-≡ S ι
SNS-PathP→SNS-≡ S ι θ {X = X} s t = ι (X , s) (X , t) (idEquiv X)           ≃⟨ θ (idEquiv X) ⟩
                                   PathP (λ i → S (ua (idEquiv X) i)) s t  ≃⟨ φ ⟩
                                   s ≡ t                                   ■
  where
   φ = transportEquiv (λ j → PathP (λ i → S (uaIdEquiv {A = X} j i)) s t)


SNS-≡→SNS-PathP : {S : Type ℓ₁ → Type ℓ₂} (ι : StrIso S ℓ₃) → SNS-≡ S ι → SNS-PathP S ι
SNS-≡→SNS-PathP {S = S} ι θ {A = A} {B = B} e = EquivJ P C (typ B) (typ A) e (str B) (str A)
  where
   P : (X Y : Type _) → Y ≃ X → Type _
   P X Y e' = (s : S X) (t : S Y) → ι (Y , t) (X , s) e' ≃ PathP (λ i → S (ua e' i)) t s

   C : (X : Type _) → (s t : S X) → ι (X , t) (X , s) (idEquiv X) ≃ PathP (λ i → S (ua (idEquiv X) i)) t s
   C X s t = ι (X , t) (X , s) (idEquiv X)           ≃⟨ θ t s ⟩
             t ≡ s                                   ≃⟨ ψ ⟩
             PathP (λ i → S (ua (idEquiv X) i)) t s  ■
    where
     ψ = transportEquiv λ j → PathP (λ i → S (uaIdEquiv {A = X} (~ j) i)) t s







-- We can now directly define a function
--    sip : A ≃[ ι ] B → A ≡ B
-- together with is inverse.
-- Here, these functions use SNS-PathP and are expressed using a Σ-type instead as it is a bit
-- easier to work with
sip : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) (θ : SNS-PathP S ι)
    → (A B : TypeWithStr ℓ₁ S)
    → A ≃[ ι ] B
    → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
sip S ι θ A B (e , p) = ua e , (θ e) .fst p

-- The inverse to sip using the following little lemma

private
  lem : (S : Type ℓ₁ → Type ℓ₂) (A B : TypeWithStr ℓ₁ S) (e : typ A ≡ typ B)
      → PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd) ≡
        PathP (λ i → S (e i)) (A .snd) (B .snd)
  lem S A B e i = PathP (λ j → S (ua-pathToEquiv e i j)) (A .snd) (B .snd)

sip⁻ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) (θ : SNS-PathP S ι)
     → (A B : TypeWithStr ℓ₁ S)
     → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
     → A ≃[ ι ] B
sip⁻ S ι θ A B (e , r) = pathToEquiv e , invEq (θ (pathToEquiv e)) q
  where
  q : PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd)
  q = transport (λ i → lem S A B e (~ i)) r


-- we can rather directly show that sip and sip⁻ are mutually inverse:
sip-sip⁻ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) (θ : SNS-PathP S ι)
         → (A B : TypeWithStr ℓ₁ S)
         → (r : Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B)))
         → sip S ι θ A B (sip⁻ S ι θ A B r) ≡ r
sip-sip⁻ S ι θ A B (p , q) =
    sip S ι θ A B (sip⁻ S ι θ A B (p , q))
  ≡⟨ refl ⟩
    ua (pathToEquiv p) , (θ (pathToEquiv p)) .fst (invEq (θ (pathToEquiv p)) (transport (λ i → lem S A B p (~ i)) q))
  ≡⟨ (λ i → ua (pathToEquiv p) , retEq (θ (pathToEquiv p)) (transport (λ i → lem S A B p (~ i)) q) i) ⟩
    ua (pathToEquiv p) , transport (λ i → lem S A B p (~ i)) q
  ≡⟨ (λ i → ua-pathToEquiv p i ,
            transp (λ k → PathP (λ j → S (ua-pathToEquiv p (i ∧ k) j)) (str A) (str B))
                   (~ i)
                   (transport (λ i → lem S A B p (~ i)) q)) ⟩
    p , transport (λ i → lem S A B p i) (transport (λ i → lem S A B p (~ i)) q)
  ≡⟨ (λ i → p , transportTransport⁻ (lem S A B p) q i) ⟩
    p , q ∎


-- The trickier direction:
sip⁻-sip : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) (θ : SNS-PathP S ι)
         → (A B : TypeWithStr ℓ₁ S)
         → (r : A ≃[ ι ] B)
         → sip⁻ S ι θ A B (sip S ι θ A B r) ≡ r
sip⁻-sip S ι θ A B (e , p) =
    sip⁻ S ι θ A B (sip S ι θ A B (e , p))
  ≡⟨ refl ⟩
    pathToEquiv (ua e) , invEq (θ (pathToEquiv (ua e))) (f⁺ p')
  ≡⟨ (λ i → pathToEquiv-ua e i , invEq (θ (pathToEquiv-ua e i)) (pth' i)) ⟩
    e , invEq (θ e) (f⁻ (f⁺ p'))
  ≡⟨ (λ i → e , invEq (θ e) (transportTransport⁻ (lem S A B (ua e)) p' i)) ⟩
    e , invEq (θ e) ((θ e) .fst p)
  ≡⟨ (λ i → e , (secEq (θ e) p i)) ⟩
    e , p ∎
  where
  p' : PathP (λ i → S (ua e i)) (str A) (str B)
  p' = (θ e) .fst p

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
SIP : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) (θ : SNS-PathP S ι)
    → (A B : TypeWithStr ℓ₁ S)
    → A ≃[ ι ] B ≃ (A ≡ B)
SIP S ι θ A B = (A ≃[ ι ] B ) ≃⟨ eq ⟩ Σ≡
  where
  eq : A ≃[ ι ] B ≃ Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
  eq = isoToEquiv (iso (sip S ι θ A B) (sip⁻ S ι θ A B)
                       (sip-sip⁻ S ι θ A B) (sip⁻-sip S ι θ A B))


-- Now, we want to add axioms (i.e. propositions) to our Structure S that don't affect the ι.
-- We use a lemma due to Zesen Qian, which can now be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83

add-to-structure : (S : Type ℓ₁ → Type ℓ₂)
                   (axioms : (X : Type ℓ₁) → S X → Type ℓ₄)
                 → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
add-to-structure S axioms X = Σ[ s ∈ S X ] (axioms X s)

add-to-iso : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃)
             (axioms : (X : Type ℓ₁) → S X → Type ℓ₄)
           → StrIso (add-to-structure S axioms) ℓ₃
add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f


add-ax-lemma : (S : Type ℓ₁ → Type ℓ₂)
               (axioms : (X : Type ℓ₁) → S X → Type ℓ₄)
               (axioms-are-Props : (X : Type ℓ₁) (s : S X) → isProp (axioms X s))
               {X Y : Type ℓ₁} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
               (f : X ≃ Y)
             → PathP (λ i → S (ua f i)) s t ≃ PathP (λ i → add-to-structure S axioms (ua f i)) (s , a) (t , b)
add-ax-lemma S axioms axioms-are-Props {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
      where
       φ : PathP (λ i → S (ua f i)) s t → PathP (λ i → add-to-structure S axioms (ua f i)) (s , a) (t , b)
       φ p i = p i , isProp→PathP (λ i → axioms-are-Props (ua f i) (p i)) a b i

       ψ : PathP (λ i → add-to-structure S axioms (ua f i)) (s , a) (t , b) → PathP (λ i → S (ua f i)) s t
       ψ r i = r i .fst

       η : section φ ψ
       η r i j =  r j .fst , isProp→isSet-PathP (λ k → axioms-are-Props (ua f k) (r k .fst)) _ _
                                                (isProp→PathP (λ k → axioms-are-Props (ua f k) (r k .fst)) a b)
                                                (λ k → r k .snd) i j

       ε : retract φ ψ
       ε p = refl


add-axioms-SNS : (S : Type ℓ₁ → Type ℓ₂)
                 (ι : (A B : Σ[ X ∈ (Type ℓ₁) ] (S X)) → A .fst ≃ B .fst → Type ℓ₃)
                 (axioms : (X : Type ℓ₁) → S X → Type ℓ₄)
                 (axioms-are-Props : (X : Type ℓ₁) (s : S X) → isProp (axioms X s))
                 (θ : SNS-PathP S ι)
               → SNS-PathP (add-to-structure S axioms) (add-to-iso S ι axioms)
add-axioms-SNS S ι axioms axioms-are-Props θ {A = (X , (s , a))} {B = (Y , (t , b))} f =
               add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f                 ≃⟨ θ f ⟩
               PathP (λ i → S (ua f i)) s t                                        ≃⟨ add-ax-lemma S axioms axioms-are-Props f ⟩
               PathP (λ i → (add-to-structure S axioms) (ua f i)) (s , a) (t , b)  ■









-- Now, we want to join two structures. Together with the adding of
-- axioms this will allow us to prove that a lot of mathematical
-- structures are a standard notion of structure

private
  technical-×-lemma : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
                    → A ≃ C → B ≃ D → A × B ≃ C × D
  technical-×-lemma {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
   where
    φ : (A × B) → (C × D)
    φ (a , b) = equivFun f a , equivFun g b

    ψ : (C × D) → (A × B)
    ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

    η : section φ ψ
    η (c , d) i = retEq f c i , retEq g d i

    ε : retract φ ψ
    ε (a , b) i = secEq f a i , secEq g b i



join-structure : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
               → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
join-structure S₁ S₂ X = S₁ X × S₂ X

join-iso : {S₁ : Type ℓ₁ → Type ℓ₂} (ι₁ : StrIso S₁ ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄} (ι₂ : StrIso S₂ ℓ₅)
         → StrIso (join-structure S₁ S₂) (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)



join-lemma :  (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
              {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (e : X ≃ Y)
            → (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂) ≃
               PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
join-lemma S₁ S₂ {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} e = isoToEquiv (iso φ ψ η ε)
   where
    φ : (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂) →
         PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
    φ (p , q) i = p i , q i

    ψ :  PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂) →
        (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
    ψ p = (λ i → p i .fst) , (λ i → p i .snd)

    η : section φ ψ
    η p = refl

    ε : retract φ ψ
    ε (p , q) = refl





join-SNS : (S₁ : Type ℓ₁ → Type ℓ₂) (ι₁ : StrIso S₁ ℓ₃) (θ₁ : SNS-PathP S₁ ι₁)
           (S₂ : Type ℓ₁ → Type ℓ₄) (ι₂ : StrIso S₂ ℓ₅) (θ₂ : SNS-PathP S₂ ι₂)
         → SNS-PathP (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS S₁ ι₁ θ₁ S₂ ι₂ θ₂ {A = (X , s₁ , s₂)} {B = (Y , t₁ , t₂)} e =
--     join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e
     (ι₁ (X , s₁) (Y , t₁) e) × (ι₂ (X , s₂) (Y , t₂) e)
  ≃⟨ technical-×-lemma (θ₁ e) (θ₂ e)  ⟩
    (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
  ≃⟨ join-lemma S₁ S₂ e ⟩
     PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂) ■
