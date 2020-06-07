{-
This is a rather literal translation of Martin Hötzel-Escardó's structure identity principle into cubical Agda. See
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

All the needed preliminary results from the lecture notes are stated and proven in this file.
It would be interesting to compare the proves with the one in Cubical.Foundations.SIP
-}



{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.EscardoSIP where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sigma.Properties


private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'


-- We prove several useful equalities and equivalences between Σ-types all the proofs are taken from
-- Martin Hötzel-Escardó's lecture notes.

-- The next result is just a reformulation of pathSigma≡sigmaPath from Sigma.Properties.

Σ-≡-≃ : {X : Type ℓ} {A : X → Type ℓ'}
       → (σ τ : Σ X A) → ((σ ≡ τ) ≃ (Σ[ p ∈ (σ .fst) ≡ (τ .fst) ] (subst A p (σ .snd) ≡ (τ .snd))))
Σ-≡-≃ {A = A} σ τ = invEquiv (ΣPathTransport≃PathΣ σ τ)



-- This cubical proof is much shorter than in HoTT but requires that A, B live in the same universe.
Σ-cong : {X : Type ℓ} {A B : X → Type ℓ'} →
         ((x : X) → (A x ≡ B x)) → (Σ X A ≡ Σ X B)
Σ-cong {X = X} p i = Σ[ x ∈ X ] (p x i)

-- Two lemmas for the more general formulation using equivalences
NatΣ : {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''}
      → ((x : X) → (A x) → (B x)) → (Σ X A) → (Σ X B)
NatΣ τ (x , a) = (x , τ x a)

Σ-to-PathP : {X : Type ℓ} {A : X → Type ℓ'} {x : X} {a b : A x}
          → (a ≡ b) → PathP (λ i → Σ X A) (x , a) (x , b)
Σ-to-PathP {x = x} p i = (x , p i)


Σ-cong-≃ :  {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} →
         ((x : X) → (A x ≃ B x)) → (Σ X A ≃ Σ X B)
Σ-cong-≃ {X = X} {A = A} {B = B} φ = isoToEquiv (iso (NatΣ f) (NatΣ g) NatΣ-ε NatΣ-η)
 where
  f : (x : X) → (A x) → (B x)
  f x = equivFun (φ x)

  g : (x : X) → (B x) → (A x)
  g x = equivFun (invEquiv (φ x))

  η : (x : X) → (a : A x) → (g x) ((f x) a) ≡ a
  η x = retEq (invEquiv (φ x))

  ε : (x : X) → (b : B x) → f x (g x b) ≡ b
  ε x = secEq  (invEquiv (φ x))

  NatΣ-η : (w : Σ X A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a)  = (x , g x (f x a)) ≡⟨ Σ-to-PathP (η x a)  ⟩
                    (x , a)           ∎

  NatΣ-ε : (u : Σ X B) → NatΣ f (NatΣ g u) ≡ u
  NatΣ-ε (x , b) = (x , f x (g x b)) ≡⟨ Σ-to-PathP (ε x b) ⟩
                   (x , b)           ∎



-- The next result is stated a bit awkwardly but is rather straightforward to prove.
Σ-change-of-variable-Iso :  {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                           → (isHAEquiv f) → (Iso (Σ X (A ∘ f)) (Σ Y A))
Σ-change-of-variable-Iso {ℓ = ℓ} {ℓ' = ℓ'} {X = X} {Y = Y} {A = A} f isHAEquivf = iso φ ψ φψ ψφ
  where
   g : Y → X
   g = isHAEquiv.g isHAEquivf
   ε : (x : X) → (g (f x)) ≡ x
   ε = isHAEquiv.sec isHAEquivf
   η : (y : Y) → f (g y) ≡ y
   η = isHAEquiv.ret isHAEquivf
   τ :  (x : X) → cong f (ε x) ≡ η (f x)
   τ = isHAEquiv.com isHAEquivf

   φ : (Σ X (A ∘ f)) → (Σ Y A)
   φ (x , a) = (f x , a)

   ψ : (Σ Y A) → (Σ X (A ∘ f))
   ψ (y , a) = (g y , subst A (sym (η y)) a)

   φψ : (z : (Σ Y A)) → φ (ψ z) ≡ z
   φψ (y , a) =
     ΣPathTransport→PathΣ _ _ (η y ,  transportTransport⁻ (λ i → A (η y i)) a)
     -- last term proves transp (λ i → A (η y i)) i0 (transp (λ i → A (η y (~ i))) i0 a) ≡ a

   ψφ : (z : (Σ X (A ∘ f))) → ψ (φ z) ≡ z
   ψφ (x , a) = ΣPathTransport→PathΣ _ _ (ε x , q)
     where
      b : A (f (g (f x)))
      b = (transp (λ i → A (η (f x) (~ i))) i0 a)

      q : transp (λ i → A (f (ε x i))) i0 (transp (λ i → A (η (f x) (~ i))) i0 a) ≡ a
      q =  transp (λ i → A (f (ε x i))) i0 b  ≡⟨ i ⟩
           transp (λ i → A (η (f x) i)) i0 b  ≡⟨ transportTransport⁻ (λ i → A (η (f x) i)) a ⟩
           a                                  ∎
       where
        i : (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (η (f x) i)) i0 b)
        i = subst (λ p → (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (p i)) i0 b))
                 (τ x) refl


-- Using the result above we can prove the following quite useful result.
Σ-change-of-variable-≃ : {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                      → (isEquiv f) → ((Σ X (A ∘ f)) ≃ (Σ Y A))
Σ-change-of-variable-≃ f isEquivf =
                      isoToEquiv (Σ-change-of-variable-Iso f (equiv→HAEquiv (f , isEquivf) .snd))




Σ-assoc-Iso : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Iso (Σ (Σ X A) P) (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))))
Σ-assoc-Iso X A P = iso f g ε η
   where
    f : (Σ (Σ X A) P) → (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
    f ((x , a) , p) = (x , (a , p))
    g : (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))) →  (Σ (Σ X A) P)
    g (x , (a , p)) = ((x , a) , p)
    ε : section f g
    ε n = refl
    η : retract f g
    η m = refl

Σ-assoc-≃ : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Σ (Σ X A) P) ≃ (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
Σ-assoc-≃ X A P = isoToEquiv (Σ-assoc-Iso X A P)




-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X, the pair (X , s)
-- means that X is equipped with a S-structure, which is witnessed by s.
-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure.


SNS : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS  {ℓ = ℓ} S ι = ∀ {X : (Type ℓ)} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))


-- Escardo's ρ can actually be  defined from this:
ρ :  {ι : StrIso S ℓ''} (θ : SNS S ι) (A : TypeWithStr ℓ S) → (ι A A (idEquiv (typ A)))
ρ θ A = equivFun (θ (str A) (str A)) refl

-- We introduce the notation a bit differently:
_≃[_]_ : (A : TypeWithStr ℓ S) (ι : StrIso S ℓ'') (B : TypeWithStr ℓ S) → (Type (ℓ-max ℓ ℓ''))
A ≃[ ι ] B = Σ[ f ∈ ((typ A) ≃ (typ B)) ] (ι A B f)



Id→homEq : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'')
          → (ρ : (A : TypeWithStr ℓ S) → ι A A (idEquiv (typ A)))
          → (A B : TypeWithStr ℓ S) → A ≡ B → (A ≃[ ι ] B)
Id→homEq S ι ρ A B p = J (λ y x → A ≃[ ι ] y) (idEquiv (typ A) , ρ A) p


-- Use a PathP version of Escardó's homomorphism-lemma
hom-lemma-dep : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
               → (A B : TypeWithStr ℓ S)
               → (p : (typ A) ≡ (typ B))
               → (PathP (λ i → S (p i)) (str A) (str B)) ≃ (ι A B (pathToEquiv p))
hom-lemma-dep S ι θ A B p = (J P (λ s → γ s) p) (str B)
     where
      P = (λ y x → (s : S y) → PathP (λ i → S (x i)) (str A) s ≃ ι A (y , s) (pathToEquiv x))

      γ : (s : S (typ A)) → ((str A) ≡ s) ≃ ι A ((typ A) , s) (pathToEquiv refl)
      γ s = subst (λ f → ((str A) ≡ s) ≃ ι A ((typ A) , s) f)  (sym pathToEquivRefl) (θ (str A) s)


-- Define the inverse of Id→homEq directly.
ua-lemma : (A B : Type ℓ) (e : A ≃ B) → (pathToEquiv (ua e)) ≡ e
ua-lemma A B e = EquivJ (λ A f → (pathToEquiv (ua f)) ≡ f)
                        (subst (λ r → pathToEquiv r ≡ idEquiv B) (sym uaIdEquiv) pathToEquivRefl)
                        e


homEq→Id : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
          → (A B : TypeWithStr ℓ S) → (A ≃[ ι ] B) → A ≡ B
homEq→Id S ι θ A B (f , φ) = ΣPathP (p , q)
        where
         p = ua f

         ψ : ι A B (pathToEquiv p)
         ψ = subst (λ g → ι A B g) (sym (ua-lemma (typ A) (typ B) f)) φ

         q : PathP (λ i → S (p i)) (str A) (str B)
         q = equivFun (invEquiv (hom-lemma-dep S ι θ A B p)) ψ


-- Proof of the SIP:
SIP : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS S ι)
     → (A B : TypeWithStr ℓ S) → ((A ≡ B) ≃ (A ≃[ ι ] B))
SIP S ι θ A B =
            (A ≡ B)                                                             ≃⟨ i ⟩
            (Σ[ p ∈ (typ A) ≡ (typ B) ] PathP (λ i → S (p i)) (str A) (str B))  ≃⟨ ii ⟩
            (Σ[ p ∈ (typ A) ≡ (typ B) ] (ι A B (pathToEquiv p)))                ≃⟨ iii ⟩
            (A ≃[ ι ] B)                                                            ■
    where
     i = invEquiv ΣPath≃PathΣ
     ii = Σ-cong-≃ (hom-lemma-dep S ι θ A B)
     iii = Σ-change-of-variable-≃ pathToEquiv (equivIsEquiv univalence)






-- A simple example: pointed types
pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

Pointed-Type : Type (ℓ-suc ℓ)
Pointed-Type {ℓ = ℓ} = Σ (Type ℓ) pointed-structure

pointed-ι : (A B : Pointed-Type) → (A .fst) ≃ (B. fst) → Type ℓ
pointed-ι (X , x) (Y , y) f = (equivFun f) x ≡ y

pointed-is-sns : SNS {ℓ = ℓ} pointed-structure pointed-ι
pointed-is-sns s t = idEquiv (s ≡ t)

pointed-type-sip : (X Y : Type ℓ) (x : X) (y : Y)
                  → (Σ[ f ∈ X ≃ Y ] (f .fst) x ≡ y) ≃ ((X , x) ≡ (Y , y))
pointed-type-sip X Y x y = invEquiv (SIP pointed-structure pointed-ι pointed-is-sns (X , x) (Y , y))
