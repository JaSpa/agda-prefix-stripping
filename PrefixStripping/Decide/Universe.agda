open import PrefixStripping.Prelude
open Relation.Binary

module PrefixStripping.Decide.Universe {𝕋 END : Set} (_≟ᵀ_ : DecidableEquality 𝕋) (_≟E_ : DecidableEquality END) where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (∈-∷⁺ʳ)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise; just; nothing)
open import Data.Unit using (⊤; tt)

open import PrefixStripping.Syntax

open import PrefixStripping.Sessions 𝕋 as Sessions hiding (𝕊; module Core; module Variables) public
open Sessions.Core END using (𝕊) public
open Sessions.Functions public
open Sessions.Equality _≟ᵀ_ using (_≟ℙ_; decSetoid-ℙ₀) public
open Sessions.EqualityCore _≟ᵀ_ _≟E_ using () renaming (_≟_ to _≟𝕊_; decSetoid₀ to decSetoid-𝕊₀) public

open import PrefixStripping.Sessions.Equivalence 𝕋 as Equivalence
open Equivalence.Decide _≟ᵀ_ _≟E_ public

open import PrefixStripping.Sessions.Subterm 𝕋 as ST using (_⊑_; ⊑-trans)
open _⊑_

infix 4 _%_

record 𝒰 : Set where
  constructor _%_
  field
    p  : ℙ 0
    s  : 𝕊 0

record ⊢𝒰 : Set where
  constructor _%_
  field
    {u} : 𝒰
    p   : ⊢ 𝒰.p u
    s   : ⊢ 𝒰.s u

𝒰⌊_⌋  = ⊢𝒰.u
𝒰⌊_⌋* = List.map 𝒰⌊_⌋

⊢𝒰-irr : ∀ {u₁ u₂} → 𝒰⌊ u₁ ⌋ ≡ 𝒰⌊ u₂ ⌋ → u₁ ≡ u₂
⊢𝒰-irr refl = cong₂ _%_ (⊢-irr _ _) (⊢-irr _ _)

module Variables where
  variable
    T : 𝕋
    p p₁ p₂ p′ : ℙ 0
    s s₁ s₂ s′ : 𝕊 0
    r r₁ r₂ r′ : 𝕊 0
    ⊢p ⊢p₁ ⊢p₂ ⊢p′ : ⊢ p
    ⊢s ⊢s₁ ⊢s₂ ⊢s′ : ⊢ s
    ⊢r ⊢r₁ ⊢r₂ ⊢r′ : ⊢ r
    θ : List ⊢𝒰

open Variables

-- We have decidable equality on universe elements.
_≟_ : DecidableEquality 𝒰
x ≟ y = map′
  (λ{ (refl , refl) → refl })
  (λ{ refl → refl , refl })
  (𝒰.p x ≟ℙ 𝒰.p y ×-dec 𝒰.s x ≟𝕊 𝒰.s y)

decSetoid : DecSetoid _ _
decSetoid = Eq.decSetoid _≟_

setoid : Setoid _ _
setoid = DecSetoid.setoid decSetoid

⊢ℝ = Maybe (Σ[ r ∈ 𝕊 0 ] ⊢ r)

variable
  𝒓 𝒓₁ 𝒓₂ 𝒓₃ 𝒓′ 𝒓″ : ⊢ℝ

infix 3.5 _≃ᴿ_

_≃ᴿ_ : Rel ⊢ℝ _
_≃ᴿ_ = Pointwise λ{ (-, x) (-, y) → x ≃ y }

≃ᴿ-trans : 𝒓₁ ≃ᴿ 𝒓₂ → 𝒓₂ ≃ᴿ 𝒓₃ → 𝒓₁ ≃ᴿ 𝒓₃
≃ᴿ-trans = PW.trans ≃-trans

infix 3.5 _⊔ᴿ_＝_

data _⊔ᴿ_＝_ : ⊢ℝ → ⊢ℝ → ⊢ℝ → Set where
  ⊔-⊥ˡ : 𝒓 ≃ᴿ 𝒓′ → nothing ⊔ᴿ 𝒓 ＝ 𝒓′
  ⊔-⊥ʳ : 𝒓 ≃ᴿ 𝒓′ → 𝒓 ⊔ᴿ nothing ＝ 𝒓′
  ⊔-≃  : ⊢s₁ ≃ ⊢r → ⊢r ≃ ⊢s₂ → just (-, ⊢s₁) ⊔ᴿ just (-, ⊢s₂) ＝ just (-, ⊢r)

⊔ᴿ-nothing⁻¹ : 𝒓₁ ⊔ᴿ 𝒓₂ ＝ nothing → 𝒓₁ ≃ᴿ nothing × 𝒓₂ ≃ᴿ nothing
⊔ᴿ-nothing⁻¹ (⊔-⊥ˡ eq) = nothing , eq
⊔ᴿ-nothing⁻¹ (⊔-⊥ʳ eq) = eq , nothing

⊔ᴿ-reflexive : 𝒓₁ ≃ᴿ 𝒓 → 𝒓₂ ≃ᴿ 𝒓 → 𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓
⊔ᴿ-reflexive {nothing} eq₁ eq₂ = ⊔-⊥ˡ eq₂
⊔ᴿ-reflexive {just _} {just _} {just _} eq₁ eq₂ = ⊔-≃ (PW.drop-just eq₁) (≃-sym (PW.drop-just eq₂))

infix 3.5 _⊢_%_＝_

data _⊢_%_＝_ (θ : List ⊢𝒰) : ⊢ p → ⊢ s → ⊢ℝ → Set where
  -- Strip-Return
  %-□ : {⊢s : ⊢ s} {⊢r : ⊢ s′} → ⊢s ≃ ⊢r → θ ⊢ ⊢□ % ⊢s ＝ just (-, ⊢r)

  -- Strip-Message
  %-♯ : let H = ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s in
    H ∉ θ →
    H ∷ θ ⊢ ⊢p % ⊢s ＝ 𝒓 →
    θ ⊢ ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s ＝ 𝒓

  -- Strip-Branching
  %-⋆ : let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    H ∉ θ →
    H ∷ θ ⊢ ⊢p₁ % ⊢s₁ ＝ 𝒓₁ →
    H ∷ θ ⊢ ⊢p₂ % ⊢s₂ ＝ 𝒓₂ →
    𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓 →
    θ ⊢ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ 𝒓

  -- Strip-UnrollR
  %-μˡ : ∀ {p} {⊢p : ⊢ p} {pᶜ : ⊢ᶜ p} →
    θ ⊢ ⊢-unfold ⊢p pᶜ % ⊢s ＝ 𝒓 →
    θ ⊢ ⊢μ ⊢p pᶜ % ⊢s ＝ 𝒓

  -- Strip-UnrollS
  %-μʳ : ∀ {s} {⊢s : ⊢ s} {sᶜ : ⊢ᶜ s} →
    θ ⊢ ⊢p % ⊢-unfold ⊢s sᶜ ＝ 𝒓 →
    θ ⊢ ⊢p % ⊢μ ⊢s sᶜ ＝ 𝒓

  -- Strip-Fix
  hyp : (⊢p % ⊢s) ∈ θ → θ ⊢ ⊢p % ⊢s ＝ nothing

⊔ᴿ-subst : ⊢r₁ ≃ ⊢r₂ → 𝒓₁ ⊔ᴿ 𝒓₂ ＝ just (-, ⊢r₁) → 𝒓₁ ⊔ᴿ 𝒓₂ ＝ just (-, ⊢r₂)
⊔ᴿ-subst eq (⊔-⊥ˡ (just eq′)) = ⊔-⊥ˡ (just (≃-trans eq′ eq))
⊔ᴿ-subst eq (⊔-⊥ʳ (just eq′)) = ⊔-⊥ʳ (just (≃-trans eq′ eq))
⊔ᴿ-subst eq (⊔-≃ eq₁ eq₂)     = ⊔-≃ (≃-trans eq₁ eq) (≃-trans (≃-sym eq) eq₂)

⊢%-subst : ⊢r₁ ≃ ⊢r₂ → θ ⊢ ⊢p % ⊢s ＝ just (-, ⊢r₁) → θ ⊢ ⊢p % ⊢s ＝ just (-, ⊢r₂)
⊢%-subst eq (%-□ eq′)             = %-□  (≃-trans eq′ eq)
⊢%-subst eq (%-♯ ∉θ p%s)          = %-♯  ∉θ (⊢%-subst eq p%s)
⊢%-subst eq (%-⋆ ∉θ p%s₁ p%s₂ 𝒓⊔) = %-⋆  ∉θ p%s₁ p%s₂ (⊔ᴿ-subst eq 𝒓⊔)
⊢%-subst eq (%-μˡ p%s)            = %-μˡ (⊢%-subst eq p%s)
⊢%-subst eq (%-μʳ p%s)            = %-μʳ (⊢%-subst eq p%s)

⊢%-substᴿ : 𝒓₁ ≃ᴿ 𝒓₂ → θ ⊢ ⊢p % ⊢s ＝ 𝒓₁ → θ ⊢ ⊢p % ⊢s ＝ 𝒓₂
⊢%-substᴿ (just eq) p%s = ⊢%-subst eq p%s
⊢%-substᴿ nothing   p%s = p%s

module PartialOrder/LeastUpperBound where
  _≤ᴿ_ : Rel ⊢ℝ _
  𝒓₁ ≤ᴿ 𝒓₂ = 𝒓₁ ≡ nothing ⊎ 𝒓₁ ≃ᴿ 𝒓₂

  ≤ᴿ-trans : 𝒓₁ ≤ᴿ 𝒓₂ → 𝒓₂ ≤ᴿ 𝒓₃ → 𝒓₁ ≤ᴿ 𝒓₃
  ≤ᴿ-trans (inj₁ eq) y           = inj₁ eq
  ≤ᴿ-trans (inj₂ eq) (inj₁ refl) = inj₁ (PW.nothing-inv (PW.sym ≃-sym eq))
  ≤ᴿ-trans (inj₂ eq) (inj₂ eq′)  = inj₂ (≃ᴿ-trans eq eq′)

  ≤-PO : IsPartialOrder _≃ᴿ_ _≤ᴿ_
  ≤-PO .IsPartialOrder.isPreorder .IsPreorder.isEquivalence  = PW.isEquivalence ≃-isEquivalence
  ≤-PO .IsPartialOrder.isPreorder .IsPreorder.reflexive      = inj₂
  ≤-PO .IsPartialOrder.isPreorder .IsPreorder.trans          = ≤ᴿ-trans
  ≤-PO .IsPartialOrder.antisym (inj₁ refl)    (inj₁ refl)    = nothing
  ≤-PO .IsPartialOrder.antisym (inj₁ refl)    (inj₂ nothing) = nothing
  ≤-PO .IsPartialOrder.antisym (inj₂ eq)      _              = eq

  open IsPartialOrder ≤-PO using (antisym) renaming (refl to ≤ᴿ-refl)

  ⊔ᴿ-⇒-infimum : 𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓 →
    ∀ 𝒓′ → 𝒓₁ ≤ᴿ 𝒓′ → 𝒓₂ ≤ᴿ 𝒓′ → 𝒓 ≤ᴿ 𝒓′
  ⊔ᴿ-⇒-infimum (⊔-⊥ˡ (just eq)) (just _) ≤₁ (inj₂ (just eq′)) = inj₂ (just (≃-trans (≃-sym eq) eq′))
  ⊔ᴿ-⇒-infimum (⊔-⊥ʳ (just eq)) (just _) (inj₂ (just eq′)) ≤₂ = inj₂ (just (≃-trans (≃-sym eq) eq′))
  ⊔ᴿ-⇒-infimum (⊔-⊥ˡ nothing)   𝒓′       ≤₁ ≤₂                = inj₁ refl
  ⊔ᴿ-⇒-infimum (⊔-⊥ʳ nothing)   𝒓′       ≤₁ ≤₂                = inj₁ refl
  ⊔ᴿ-⇒-infimum (⊔-≃ eq₁ eq₂) (just x) (inj₂ eq₁′) (inj₂ eq₂′) = inj₂ (just (≃-trans eq₂ (PW.drop-just eq₂′)))

  infimum-⇒-⊔ᴿ : 𝒓₁ ≤ᴿ 𝒓 → 𝒓₂ ≤ᴿ 𝒓 → (∀ {𝒓′} → 𝒓₁ ≤ᴿ 𝒓′ → 𝒓₂ ≤ᴿ 𝒓′ → 𝒓 ≤ᴿ 𝒓′) →
    𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓
  infimum-⇒-⊔ᴿ (inj₁ refl) ≤₂         is-inf = ⊔-⊥ˡ (antisym ≤₂ (is-inf (inj₁ refl) ≤ᴿ-refl))
  infimum-⇒-⊔ᴿ (inj₂ eq₁) (inj₁ refl) is-inf = ⊔-⊥ʳ (antisym (inj₂ eq₁) (is-inf ≤ᴿ-refl (inj₁ refl)))
  infimum-⇒-⊔ᴿ (inj₂ eq₁) (inj₂ eq₂)  is-inf = ⊔ᴿ-reflexive eq₁ eq₂

  nothing≤ᴿ : nothing ≤ᴿ 𝒓
  nothing≤ᴿ = inj₁ refl


record RemPaths (⊢p : ⊢ p) (⊢s : ⊢ s) (⊢r : ⊢ r) : Set where
  field
    {returnPath} : RawPath
    returnPath∈p : Path returnPath p
    returnPath∈s : Path returnPath s
    –[returnPath]→□ : ⊢p –[ returnPath∈p ]→ ⊢□
    –[returnPath]→r : ⊢s –[ returnPath∈s ]→ ⊢r

remPaths-□ : ⊢s ≃ ⊢r → RemPaths ⊢□ ⊢s ⊢r
remPaths-□ eq = record
  { returnPath      = []
  ; returnPath∈p    = _
  ; returnPath∈s    = _
  ; –[returnPath]→□ = ≃-refl
  ; –[returnPath]→r = eq
  }

liftRemPaths : {⊢p : ⊢ p} {⊢s : ⊢ s} (sᵖ : Step 𝓢 p) (sˢ : Step 𝓢 s)
  → RemPaths (⊢-target ⊢p sᵖ) (⊢-target ⊢s sˢ) ⊢r
  → RemPaths ⊢p ⊢s ⊢r
liftRemPaths sᵖ sˢ rp =
  let open RemPaths rp in
  record
   { returnPath∈p    = sᵖ , returnPath∈p
   ; returnPath∈s    = sˢ , returnPath∈s
   ; –[returnPath]→□ = –[returnPath]→□
   ; –[returnPath]→r = –[returnPath]→r
   }

substRemPaths : ⊢p₁ ≃ ⊢p₂ → ⊢s₁ ≃ ⊢s₂ → ⊢r₁ ≃ ⊢r₂ → RemPaths ⊢p₁ ⊢s₁ ⊢r₁ → RemPaths ⊢p₂ ⊢s₂ ⊢r₂
substRemPaths eqᵖ eqˢ eqʳ rp =
  let open RemPaths rp in
  record
   { returnPath∈p    = ≃-path eqᵖ returnPath∈p
   ; returnPath∈s    = ≃-path eqˢ returnPath∈s
   ; –[returnPath]→□ = ≃-trans (≃-sym (≃-target* eqᵖ returnPath∈p)) –[returnPath]→□
   ; –[returnPath]→r = ≃-trans (≃-sym (≃-target* eqˢ returnPath∈s)) (≃-trans –[returnPath]→r eqʳ)
   }

remPaths : θ ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → RemPaths ⊢p ⊢s ⊢r
remPaths (%-□ eq) = remPaths-□ eq
remPaths (%-♯ _ p%s) = liftRemPaths step-♯ step-♯ (remPaths p%s)
remPaths (%-⋆ _ %₁ %₂ (⊔-⊥ˡ (just eq))) =
  liftRemPaths step-⋆₂ step-⋆₂
    (substRemPaths ≃-refl ≃-refl eq (remPaths %₂))
remPaths (%-⋆ _ %₁ %₂ (⊔-⊥ʳ (just eq))) =
  liftRemPaths step-⋆₁ step-⋆₁
    (substRemPaths ≃-refl ≃-refl eq (remPaths %₁))
remPaths (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) =
  liftRemPaths step-⋆₁ step-⋆₁
    (substRemPaths ≃-refl ≃-refl eq₁ (remPaths %₁))
remPaths (%-μˡ {⊢p = p} {pᶜ} p%s) =
  substRemPaths (≃-sym (≃-μ p pᶜ)) ≃-refl ≃-refl (remPaths p%s)
remPaths (%-μʳ {⊢s = s} {sᶜ} p%s) =
  substRemPaths ≃-refl (≃-sym (≃-μ s sᶜ)) ≃-refl (remPaths p%s)

remPaths-r≄ : ⊢r₁ ≄ ⊢r₂ → RemPaths ⊢p₁ ⊢s₁ ⊢r₁ → RemPaths ⊢p₂ ⊢s₂ ⊢r₂ →
  ∀ {r} {⊢r : ⊢ r} →
    ⊢[ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ ◇ ⊢r ] ≄ ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩
remPaths-r≄ r₁≄r₂ paths₁ paths₂ {r} {⊢r} =
  let module P₁ = RemPaths paths₁ in
  let module P₂ = RemPaths paths₂ in
  targets*≄-⇒-≄
    (step-⋆₁ , path◇ P₁.returnPath∈p r)
    (step-⋆₂ , path◇ P₂.returnPath∈p r)
    (step-⋆₁ , P₁.returnPath∈s)
    (step-⋆₂ , P₂.returnPath∈s)
    (≃-trans
          (◇s–[π→□]→s _ P₁.returnPath∈p P₁.–[returnPath]→□)
          (≃-sym (◇s–[π→□]→s _ P₂.returnPath∈p P₂.–[returnPath]→□)))
    (λ eq → r₁≄r₂ (≃-trans (≃-sym P₁.–[returnPath]→r) (≃-trans eq P₂.–[returnPath]→r)))
