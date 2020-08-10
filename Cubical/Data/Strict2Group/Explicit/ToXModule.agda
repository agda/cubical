
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Explicit.ToXModule where

open import Cubical.Foundations.Prelude hiding (comp)

open import Cubical.Data.Group.Base
open import Cubical.Data.XModule.Base
open import Cubical.Data.Group.Action.Base
open import Cubical.Data.Sigma

open import Cubical.Data.Strict2Group.Explicit.Base
open import Cubical.Data.Strict2Group.Explicit.Interface

Strict2GroupExp→XModuleExp : {ℓ : Level} (S : Strict2GroupExp ℓ) → (XModuleExp ℓ)
Strict2GroupExp→XModuleExp (strict2groupexp C₀ C₁ s t i ∘ si ti s∘ t∘ isMorph∘ assoc∘ lUnit∘ rUnit∘) =
  record
    { G = C₀ ;
    H = ks ;
    τ = tₖₛ ;
    α = laction
      (λ g h → lAction.act lad (id g) h)
      (λ h →
         ΣPathP (p1 h ,
           isProp→PathP
             (λ i → snd (P (p1 h i)))
             (kerIsNormal {G = C₁} {H = C₀} s (id 1₀) h)
             (kerIsNormal {G = C₁} {H = C₀} s 1₁ h))
         ∙ lAction.identity lad h)
      (λ g g' h →
         ΣPathP (p2 g g' h ,
           isProp→PathP
             (λ i → snd (P (p2 g g' h i)))
             (kerIsNormal {G = C₁} {H = C₀} s (id (g ∙₀ g')) h)
             (kerIsNormal {G = C₁} {H = C₀} s (id g ∙₁ id g') h))
         ∙ (lAction.coh lad (id g) (id g') h))
      λ g h h' → lAction.hom lad (id g) h h' ;
    equivar = equivar ;
    peiffer = pf }
      where
        S = strict2groupexp C₀ C₁ s t i ∘ si ti s∘ t∘ isMorph∘ assoc∘ lUnit∘ rUnit∘
        open S2GInterface S
        -- the kernel of the source map
        kers = ker {G = C₁} {H = C₀} s
        -- the family of propositions ker(x) ≡ 1
        P = Subgroup.typeProp kers
        -- kernel coerced to group
        ks = Subgroup→Group {G = C₁} kers

        -- the left adjoint action of hom on its normal subgroup ker(src)
        lad : lAction C₁ ks
        lad = lActionAdjSubgroup C₁ kers (kerIsNormal {G = C₁} {H = C₀} s)

        -- the target map restricted to ker(src)
        tₖₛ = restrictGroupMorph {G = C₁} {H = C₀} t kers
        tarₖₛ = fst tₖₛ
        tar∙ₖₛ = snd tₖₛ
        -- multiplication, inverse in ker src
        _∙₁ₖₛ_ = isGroup.comp (Group.groupStruc ks)
        ks⁻¹ = isGroup.inv (Group.groupStruc ks)
        -- group laws in ker(src)
        lUnitₖₛ = isGroup.lUnit (Group.groupStruc ks)
        rUnitₖₛ = isGroup.rUnit (Group.groupStruc ks)
        rCancelₖₛ = isGroup.rCancel (Group.groupStruc ks)
        assocₖₛ = isGroup.assoc (Group.groupStruc ks)
        1ₖₛ = isGroup.id (Group.groupStruc ks)

        -- Composition restricted to ks×₀ks
        ∘ₖₛ : (g f : Group.type ks) → (src (fst g) ≡ tarₖₛ f) → Group.type ks
        ∘ₖₛ g f coh = (⊙' (fst g) (fst f) coh) , ((src⊙' (fst g) (fst f) coh) ∙ snd f)

        -- right and left unit law for restricted ∘
        abstract
          rUnit∘ₖₛ : (h : Group.type ks) →
            ∘ₖₛ h (id (src (fst h)) , si (src (fst h)) ∙ snd h)
              (sym (ti (src (fst h)))) ≡ h
          rUnit∘ₖₛ h = ΣPathP (rUnit∘ (fst h) ,
            isProp→PathP
              (λ i → snd (P (rUnit∘ (fst h) i)))
              (src⊙' (fst h) (id (src (fst h))) (sym (ti (src (fst h)))) ∙ si (src (fst h)) ∙ snd h)
              (snd h))
        abstract
          lUnit∘ₖₛ : (h : Group.type ks) →
            (⊙ (co (id (tar (fst h))) (fst h) (si (tar (fst h)))) , (src⊙' (id (tar (fst h))) (fst h) (si (tar (fst h)))) ∙ snd h) ≡ h
          lUnit∘ₖₛ h = ΣPathP (
            lUnit∘ (fst h) ,
            isProp→PathP
              (λ i → snd (P (lUnit∘ (fst h) i))) (src⊙' (id (tar (fst h))) (fst h) (si (tar (fst h))) ∙ snd h) (snd h))

        -- two proofs used in equivariant
        abstract
          p1 = λ (h : Group.type ks) → cong (λ z → (z ∙₁ fst h) ∙₁ (C₁⁻¹ z)) (morphId {G = C₀} {H = C₁} i)
          p2 = λ (g g' : Group.type C₀) (h : Group.type ks) → cong (λ z → (z ∙₁ fst h) ∙₁ (C₁⁻¹ z)) (id∙₀ g g')

          equivar = λ g h → tar∙₁ (id g ∙₁ fst h) (C₁⁻¹ (id g)) ∙∙
            cong (_∙₀ (tar (C₁⁻¹ (id g)))) (tar∙₁ (id g) (fst h)) ∙∙
            cong (((tar (id g)) ∙₀ (tar (fst h))) ∙₀_) (morphInv {G = C₁} {H = C₀} t (id g)) ∙
            cong (λ z → (z ∙₀ (tar (fst h))) ∙₀ (C₀⁻¹ z)) (ti g)

        -- the peiffer identity, proved according to
        -- ixh'ix- ≡ eixh'ix- ≡ hh-ixh'ix- ≡ hh-ixh'ixe

          pf : (h h' : Group.type ks) → lAction.act lad (id (tarₖₛ h)) h' ≡ (h ∙₁ₖₛ h') ∙₁ₖₛ (ks⁻¹ h)
          pf h h' =
            ixh'ix-
              ≡⟨ sym (lUnitₖₛ ixh'ix-) ⟩
            1ₖₛ ∙₁ₖₛ ixh'ix-
              ≡⟨ cong (_∙₁ₖₛ ixh'ix-) (sym (rCancelₖₛ h)) ⟩
            (h ∙₁ₖₛ h-) ∙₁ₖₛ ixh'ix-
              ≡⟨ assocₖₛ h h- ixh'ix- ⟩
            h ∙₁ₖₛ (h- ∙₁ₖₛ ixh'ix-)
              ≡⟨ cong (h ∙₁ₖₛ_) (
                h- ∙₁ₖₛ ixh'ix-
                  ≡⟨ cong (h- ∙₁ₖₛ_) (sym (rUnit∘ₖₛ ixh'ix-)) ⟩
                h- ∙₁ₖₛ (∘ₖₛ ixh'ix- (is ixh'ix-) (src≡tarIdSrc (fst ixh'ix-)))
                  ≡⟨ cong (_∙₁ₖₛ (∘ₖₛ ixh'ix- (is ixh'ix-) (src≡tarIdSrc (fst ixh'ix-)))) (sym (lUnit∘ₖₛ h-)) ⟩
                (⊙ ix-⊙h-₁ , (src⊙ ix-⊙h-₁) ∙ snd h-) ∙₁ₖₛ ∘ₖₛ ixh'ix- (is ixh'ix-) (src≡tarIdSrc (fst ixh'ix-))
                  ≡⟨ ΣPathP (q3 , isProp→PathP (λ i → snd (P (q3 i))) (snd ((ix-∘h-₁ , (src⊙ ix-⊙h-₁) ∙ snd h-) ∙₁ₖₛ ∘ₖₛ ixh'ix- (is ixh'ix-) (src≡tarIdSrc (fst ixh'ix-)))) (src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ fst (is ixh'ix-)) q1 ∙ q2)) ⟩
                (⊙ (co (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ fst (is ixh'ix-)) q1)) , (src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ fst (is ixh'ix-)) q1) ∙ q2
                  ≡⟨ ΣPathP (q18 , (isProp→PathP (λ j → snd (P (q18 j))) ((src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ fst (is ixh'ix-)) q1) ∙ q2) ((src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ 1₁) (q5 ∙ q8)) ∙ q9))) ⟩
                (⊙ (co (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ 1₁) (q5 ∙ q8))) ,
                  (src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ 1₁) (q5 ∙ q8)) ∙ q9
                  ≡⟨ ΣPathP (q17 , (isProp→PathP (λ j → snd (P (q17 j))) ((src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ 1₁) (q5 ∙ q8)) ∙ q9) ((src⊙' (ix- ∙₁ fst ixh'ix-) (fst h-) q5) ∙ snd h-))) ⟩
                (⊙ (co (ix- ∙₁ fst ixh'ix-) (h- .fst) q5)) ,
                  (src⊙' (ix- ∙₁ fst ixh'ix-) (h- .fst) q5)  ∙ snd h-
                  ≡⟨ ΣPathP (q16 , isProp→PathP (λ j → snd (P (q16 j))) ((src⊙' (ix- ∙₁ fst ixh'ix-) (fst h-) q5) ∙ snd h-) ((src⊙' (ix- ∙₁ fst ixh'ix-) (1₁ ∙₁ h- .fst) (q5 ∙ q6)) ∙ q7)) ⟩
                (⊙ (co (ix- ∙₁ fst ixh'ix-) (1₁ ∙₁ h- .fst) (q5 ∙ q6))) ,
                  (src⊙' (ix- ∙₁ fst ixh'ix-) (1₁ ∙₁ h- .fst) (q5 ∙ q6)) ∙ q7
                  ≡⟨ ΣPathP (q15 , (isProp→PathP (λ j → snd (P (q15 j))) ((src⊙' (ix- ∙₁ fst ixh'ix-) (1₁ ∙₁ h- .fst) (q5 ∙ q6)) ∙ q7) ((src⊙' ((fst h') ∙₁ ix-) (1₁ ∙₁ h- .fst) q4) ∙ q7))) ⟩
                (⊙ (co ((fst h') ∙₁ ix-) (1₁ ∙₁ h- .fst) q4)) ,
                  (src⊙' ((fst h') ∙₁ ix-) (1₁ ∙₁ h- .fst) q4) ∙ q7
                  ≡⟨ ΣPathP (q14 , isProp→PathP (λ j → snd (P (q14 j))) ((src⊙' ((fst h') ∙₁ ix-) (1₁ ∙₁ h- .fst) q4) ∙ q7) q12) ⟩
                (⊙ (co (fst h') 1₁ ((snd h') ∙ (sym tar1₁≡1₀)))) ∙₁ ix-∘h-₁ , q12
                  ≡⟨ ΣPathP (q11 , isProp→PathP (λ j → snd (P (q11 j))) q12 q13) ⟩
                h' .fst ∙₁ ix-∘h-₁ , q13
                  ≡⟨ ΣPathP (q10 , isProp→PathP (λ j → snd (P (q10 j)))
                    (src∙₁ (fst h') ix-∘h-₁ ∙∙
                      (λ i₁ → snd h' i₁ ∙₀ src ix-∘h-₁) ∙∙
                      lUnit₀ (src ix-∘h-₁) ∙∙
                      src⊙ ix-⊙h-₁ ∙∙
                      snd h-)
                    (Subgroup.compClosed kers h' h-)) ⟩
                h' .fst ∙₁ h- .fst , Subgroup.compClosed kers h' h- ≡⟨ refl ⟩
                (h' ∙₁ₖₛ h-) ≡⟨ refl ⟩ refl ) ⟩
              h ∙₁ₖₛ (h' ∙₁ₖₛ h-)
              ≡⟨ sym (assocₖₛ h h' h-) ⟩
            (h ∙₁ₖₛ h') ∙₁ₖₛ h- ≡⟨ refl ⟩ refl
            where
              -- some abbreviations
            h- = ks⁻¹ h -- h⁻¹
            x = tarₖₛ h -- target of h
            x- = tarₖₛ h- -- target of h⁻¹
            x-≡x⁻¹ : x- ≡ C₀⁻¹ x
            x-≡x⁻¹ = morphInv {G = ks} {H = C₀} tₖₛ h
            ix = id x -- i (t h)
            ix- = id x- -- i (t h⁻¹)
            ixh'ix- : Group.type ks -- abv. for (ix ∙₁ h') ∙₁ ix-
            ixh'ix- = lAction.act lad (id (tarₖₛ h)) h'
            is : Group.type ks → Group.type ks -- abv. for i(s _) in ks
            is h = id (src (fst h)) , (si (src (fst h))) ∙ snd h
            ix-⊙h-₁ = co ix- (fst h-) (si x-)
            ix-∘h-₁ = ⊙ ix-⊙h-₁

            -- some identities
            ix-≡ix⁻¹ : ix- ≡ (C₁⁻¹ ix)
            ix-≡ix⁻¹ = (cong id x-≡x⁻¹) ∙ (morphInv {G = C₀} {H = C₁} i x)
            ish≡1ₖₛ : (h : Group.type ks) → (is h) ≡ 1ₖₛ
            ish≡1ₖₛ h =
              ΣPathP
                (cong (fst i) (snd h) ∙ id1₀≡1₁ ,
                isProp→PathP
                  (λ j → snd (P (((λ k → id(snd h k)) ∙ id1₀≡1₁) j)))
                  (si (src (fst h)) ∙ snd h)
                  (Subgroup.subId kers))
            -- t h⁻¹ ≡ (t h)⁻¹
            th-≡x- = morphInv {G = ks} {H = C₀} tₖₛ h

            -----------------------------------------
            -- here comes particles of the main proof
            -----------------------------------------

            -- coherence condition for the composition
            -- ∘ (ix- ∙₁ fst ixh'ix-) (h- .fst ∙₁ fst (is ixh'ix-))
            q1 =
              src∙₁ ix- (fst ixh'ix-) ∙∙
              cong (_∙₀ src (fst ixh'ix-)) (si x-) ∙∙
              cong (x- ∙₀_) (snd ixh'ix-) ∙∙
              rUnit₀ x- ∙∙
              th-≡x- ∙∙
              sym (rUnit₀ (C₀⁻¹ x)) ∙∙
              cong ((C₀⁻¹ x) ∙₀_) (sym ((ti ((src (fst ixh'ix-)))) ∙ (snd ixh'ix-))) ∙∙
              cong (_∙₀ (tar (fst (is ixh'ix-)))) (sym th-≡x-) ∙∙
              sym (tar∙₁ (fst h-) (fst (is ixh'ix-)))

            -- to show that ∘ q1 is in ks, p2 is proof that f is in ks
            q2 = src∙₁ (fst h-) (fst (is ixh'ix-)) ∙∙
              cong (_∙₀ (src (fst (is ixh'ix-)))) (snd h-) ∙∙
              lUnit₀ (src (fst (is ixh'ix-))) ∙∙
              cong (λ z → src (fst z)) (ish≡1ₖₛ ixh'ix-) ∙∙
              snd 1ₖₛ

            -- (∘ (si x-)) ∙₁ (fst (∘ₖₛ (src≡tarIdSrc (fst ixh'ix-)))) ≡ ∘ q1
            q3 =
              (ix-∘h-₁ ∙₁ fst (∘ₖₛ ixh'ix- (is ixh'ix-) (src≡tarIdSrc (fst ixh'ix-)))) ≡⟨ refl ⟩
              ⊙ ix-⊙h-₁ ∙₁ ⊙ co3
                ≡⟨ sym (isMorph⊙ ix-⊙h-₁ co3) ⟩
              ⊙ (ix-⊙h-₁ ∙Co co3)
                ≡⟨ ⊙≡c (ix-⊙h-₁ ∙Co co3) q1 ⟩
              ⊙ co1 ≡⟨ refl ⟩ refl
              where
                co1 = co (ix- ∙₁ fst ixh'ix-) (fst h- ∙₁ fst (is ixh'ix-)) q1
                co3 = co (fst ixh'ix-) (fst (is ixh'ix-)) (src≡tarIdSrc (fst ixh'ix-))

            -- coherence condition for ∘ {g = ?} {f = 1₁ ∙₁ h- .fst} (_∙ q6)
            q6 = sym (lUnit₀ (tar (fst h-))) ∙∙
                 sym (cong (_∙₀ (tar (fst h-))) (morphId {G = C₁} {H = C₀} t)) ∙∙
                 sym (tar∙₁ 1₁ (fst h-))

            -- coherence condition for ∘ {g = (fst h') ∙₁ ix- } {f = 1₁ ∙₁ h- .fst } q4
            q4 =
              src∙₁ (fst h') ix- ∙∙
              (cong (_∙₀ src ix-) (snd h')) ∙∙
              lUnit₀ (src ix-) ∙∙
              si x- ∙∙
              q6

            -- coherence condition for ∘ {g = ix- ∙₁ fst ixh'ix- } {f = ?} (q5 ∙ ?)
            q5 =
              src∙₁ ix- (fst ixh'ix-) ∙∙
              cong ((src ix-) ∙₀_) (snd ixh'ix-) ∙∙
              rUnit₀ (src ix-) ∙
              si x-

            -- proof that 1₁ ∙₁ h- .fst : ker s
            q7 = src∙₁ 1₁ (fst h-) ∙∙
              cong (src 1₁ ∙₀_) (snd h-) ∙∙
              rUnit₀ (src 1₁) ∙ src1₁≡1₀

            -- proof that s x- ≡ t (h- .fst ∙₁ 1₁)
            q8 = sym (rUnit₀ (tar (fst h-))) ∙∙
              (sym (cong ((tar (fst h-)) ∙₀_) tar1₁≡1₀)) ∙∙
              (sym (tar∙₁ (fst h-) 1₁))

            -- proof that h- .fst ∙₁ 1₁ : ker s
            q9 = src∙₁ (fst h-) 1₁ ∙∙
              cong (_∙₀ (src 1₁)) (snd h-) ∙∙
              lUnit₀ (src 1₁) ∙
              src1₁≡1₀

            -- proof that (h' .fst ∙₁ ix-∘h-₁) ≡ (h' .fst ∙₁ h- .fst)
            q10 = cong (h' .fst ∙₁_) (lUnit∘ (fst h-))

            -- proof that (h'∘1₁)∙₁ ix-∘h-₁ ≡ h' ‌‌‌∙₁ ix-∘h-₁
            q11 = cong (_∙₁ ix-∘h-₁)
                       (⊙≡ (co (fst h') 1₁ (snd h' ∙ sym tar1₁≡1₀)) (id (src (fst h')) , sym id1₀≡1₁ ∙ sym (cong id (snd h'))) ∙
                       rUnit⊙c
                         (fst h')
                         ((snd h' ∙ (λ i₁ → tar1₁≡1₀ (~ i₁))) ∙ cong tar ((λ i₁ → id1₀≡1₁ (~ i₁)) ∙ (λ i₁ → id (snd h' (~ i₁))))))


            q12 =
                src∙₁ ((⊙ (co (fst h') 1₁ ((snd h') ∙ sym tar1₁≡1₀)))) ix-∘h-₁ ∙∙
                cong (_∙₀ (src ix-∘h-₁)) ((src⊙' (fst h') 1₁ ((snd h') ∙ (sym tar1₁≡1₀))) ∙  src1₁≡1₀) ∙∙
                lUnit₀ (src ix-∘h-₁) ∙
                src⊙' ix- (fst h-) (si x-) ∙ snd h-

            q13 = src∙₁ (fst h') ix-∘h-₁ ∙∙
              cong (_∙₀ (src ix-∘h-₁)) (snd h') ∙∙
              lUnit₀ (src ix-∘h-₁) ∙∙
              src⊙' ix- (fst h-) (si x-) ∙∙
              snd h-

            q14 =
              ⊙' ((fst h') ∙₁ ix-) (1₁ ∙₁ h- .fst) q4
                ≡⟨ ⊙≡c~ q4 (𝒸 (co (fst h') 1₁ (snd h' ∙ (λ i₁ → tar1₁≡1₀ (~ i₁))) ∙Co ix-⊙h-₁)) ⟩
              ⊙' ((fst h') ∙₁ ix-) (1₁ ∙₁ (fst h-)) (𝒸 (co (fst h') 1₁ (snd h' ∙ (λ i₁ → tar1₁≡1₀ (~ i₁))) ∙Co ix-⊙h-₁))
                ≡⟨ isMorph⊙ (co (fst h') 1₁ (snd h' ∙ (λ i₁ → tar1₁≡1₀ (~ i₁)))) ix-⊙h-₁ ⟩
             -- (⊙' (fst h') 1₁ (snd h' ∙ (λ i₁ → tar1₁≡1₀ (~ i₁)))) ∙₁ ix-∘h-₁ ≡⟨ refl ⟩
              refl

            q15 = ≡⊙c* (q5 ∙ q6)
                  (cong (ix- ∙₁_) (assoc₁ ix (fst h') (C₁⁻¹ ix)) ∙∙
                    sym (assoc₁ ix- ix (fst h' ∙₁ C₁⁻¹ ix)) ∙∙
                    cong (λ z → (z ∙₁ ix) ∙₁ (fst h' ∙₁ C₁⁻¹ ix)) ix-≡ix⁻¹ ∙∙
                    cong (_∙₁ (fst h' ∙₁ C₁⁻¹ ix)) (lCancel₁ ix) ∙∙
                    lUnit₁ (fst h' ∙₁ C₁⁻¹ ix) ∙
                    cong (fst h' ∙₁_) (sym ix-≡ix⁻¹))
                  q4
              {- use this to see what's going on
              ⊙ co1
                ≡⟨ ≡⊙c* (q5 ∙ q6)
                  ((cong (ix- ∙₁_) (assoc₁ ix (fst h') (C₁⁻¹ ix))) ∙
                    sym (assoc₁ ix- ix (fst h' ∙₁ C₁⁻¹ ix)) ∙
                    cong (λ z → (z ∙₁ ix) ∙₁ (fst h' ∙₁ C₁⁻¹ ix)) ix-≡ix⁻¹ ∙
                    cong (_∙₁ (fst h' ∙₁ C₁⁻¹ ix)) (lCancel₁ ix) ∙
                    (lUnit₁ (fst h' ∙₁ C₁⁻¹ ix)) ∙
                    (cong (fst h' ∙₁_) (sym ix-≡ix⁻¹)))
                  q4 ⟩
              ⊙ co2 ≡⟨ refl ⟩ refl
              where
                co1 = co (ix- ∙₁ (fst ixh'ix-)) (1₁ ∙₁ (fst h-)) (q5 ∙ q6)
                co2 = co ((fst h') ∙₁ ix-) (1₁ ∙₁ (fst h-)) q4 -}

            q16 = ⊙≡c* q5 (sym (lUnit₁ (fst h-))) (q5 ∙ q6)
              {- use this to see what's going on
              ⊙ co1
                ≡⟨ ⊙≡c* q5 (sym (lUnit₁ (fst h-))) (q5 ∙ q6) ⟩
              ⊙ co2 ≡⟨ refl ⟩ refl
              where
                co1 = co (ix- ∙₁ fst ixh'ix-) (fst h-) q5
                co2 = co (ix- ∙₁ fst ixh'ix-) (1₁ ∙₁ fst h-) (q5 ∙ q6) -}

            q17 = ⊙≡c* (q5 ∙ q8) (rUnit₁ (fst h-)) q5
              {- use this to see what's going on
              ⊙ co1
                ≡⟨ ⊙≡c* (q5 ∙ q8) (rUnit₁ (fst h-)) q5 ⟩
              ⊙ co2 ≡⟨ refl ⟩ refl
              where
                co1 = co (ix- ∙₁ fst ixh'ix-) (fst h- ∙₁ 1₁) (q5 ∙ q8)
                co2 = co (ix- ∙₁ fst ixh'ix-) (fst h-) q5 -}

            q18 = ⊙≡c* q1 (cong (fst h- ∙₁_) ((cong id (snd ixh'ix-)) ∙ id1₀≡1₁)) (q5 ∙ q8)
              {- use this to see what's going on
              ⊙ co1 ≡⟨ ⊙≡c* q1 (cong (fst h- ∙₁_)
                ((cong id (snd ixh'ix-)) ∙ id1₀≡1₁))
                (q5 ∙ q8) ⟩
              ⊙ co2 ≡⟨ refl ⟩ refl
              where
                co1 = co (ix- ∙₁ fst ixh'ix-) (fst h- ∙₁ (fst (is ixh'ix-))) q1
                co2 = co (ix- ∙₁ fst ixh'ix-) (fst h- ∙₁ 1₁) (q5 ∙ q8) -}
