open import Data.Nat

data Int : Set where
  swap    : Int
  clone   : Int
  drop    : Int
  quot    : Int
  compose : Int
  apply   : Int

infix  5 [_]
infixl 7 _∘_
infix  9 `_

data Expr : Set where

  `_  : Int → Expr

  [_] : Expr → Expr

  _∘_ : Expr → Expr → Expr

data Value : Expr → Set where

  ⟦_⟧ : (e : Expr) → Value [ e ]

infixl 4 _,_

data Stack : Set where

  ⟨⟩  : Stack

  _,_ : ∀ {e}
      → (V : Stack)
      → (v : Value e)
      → Stack

infix 3 ⟨_⟩_→⟨_⟩

data ⟨_⟩_→⟨_⟩ : Stack → Expr → Stack → Set where

  i-swap : ∀ {V e e′}
         → (v : Value e)
         → (v′ : Value e′)
           -------------------------------------
         → ⟨ V , v , v′ ⟩ ` swap →⟨ V , v′ , v ⟩

  i-clone : ∀ {V e}
          → (v : Value e)
            --------------------------------
          → ⟨ V , v ⟩ ` clone →⟨ V , v , v ⟩

  i-drop : ∀ {V e}
           → (v : Value e)
             ---------------------------
           → ⟨ V , v ⟩ ` drop →⟨ V ⟩

  i-quote : ∀ {V e}
            → (v : Value e)
              -----------------------------------
            → ⟨ V , v ⟩ ` quot →⟨ V , ⟦ e ⟧ ⟩

  i-compose : ∀ {V e e′}
              ----------------------------------------------------
            → ⟨ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟩ ` compose →⟨ V , ⟦ e ∘ e′ ⟧ ⟩

  i-apply : ∀ {V V′ e}
          → ⟨ V ⟩ e →⟨ V′ ⟩
            -----------------------------
          → ⟨ V , ⟦ e ⟧ ⟩ ` apply →⟨ V′ ⟩

  e-quote : ∀ {V e}
            --------------------------
          → ⟨ V ⟩ [ e ] →⟨ V , ⟦ e ⟧ ⟩

  _e-∘_ : ∀ {V V′ W e e′}
        → ⟨ V  ⟩ e  →⟨ V′ ⟩
        → ⟨ V′ ⟩ e′ →⟨ W  ⟩
          -------------------
        → ⟨ V ⟩ e ∘ e′ →⟨ W ⟩

⊥ : Expr
⊥ = [ ` drop ]

⊥ᵥ : Value ⊥
⊥ᵥ = ⟦ ` drop ⟧

⊤ : Expr
⊤ = [ ` swap ∘ ` drop ]

⊤ᵥ : Value ⊤
⊤ᵥ = ⟦ ` swap ∘ ` drop ⟧

⊥-thm : ∀ {V e e′}
      → (v : Value e)
      → (v′ : Value e′)
      → ⟨ V , v , v′ ⟩ ⊥ ∘ ` apply →⟨ V , v ⟩
⊥-thm {V} v v′ = e-quote e-∘ i-apply (i-drop v′)

⊤-thm : ∀ {V e e′}
      → (v : Value e)
      → (v′ : Value e′)
      → ⟨ V , v , v′ ⟩ ⊤ ∘ ` apply →⟨ V , v′ ⟩
⊤-thm {V} {e} {e′} v v′ = e-quote e-∘ i-apply (i-swap v v′ e-∘ i-drop v)

∨ : Expr
∨ = ` clone ∘ ` apply

∨-⊥-⊥ : ∀ {V e} → ⟨ V , ⟦ e ⟧ , ⊥ᵥ ⟩ ∨ →⟨ V , ⟦ e ⟧ ⟩
∨-⊥-⊥ = i-clone ⟦ ` drop ⟧ e-∘ i-apply (i-drop ⟦ ` drop ⟧)

∨-⊤ : ∀ {V e} → ⟨ V , ⟦ e ⟧ , ⊤ᵥ ⟩ ∨ →⟨ V , ⊤ᵥ ⟩
∨-⊤ {V} {e} = i-clone ⟦ ` swap ∘ ` drop ⟧ e-∘
                i-apply (i-swap ⟦ e ⟧ ⟦ ` swap ∘ ` drop ⟧ e-∘ i-drop ⟦ e ⟧)

quoteₙ : ℕ → Expr
quoteₙ zero = ` quot
quoteₙ (suc n) = quoteₙ n ∘ ` swap ∘ ` quot ∘ ` swap ∘ ` compose

quote₂-thm : ∀ {V e e′}
           → (v : Value e)
           → (v′ : Value e′)
             -------------------------------------------
           → ⟨ V , v , v′ ⟩ quoteₙ 1 →⟨ V , ⟦ e ∘ e′ ⟧ ⟩
quote₂-thm {V} {e} {e′} v v′ = (((i-quote v′ e-∘ i-swap v ⟦ e′ ⟧) e-∘ i-quote v) e-∘
                                  i-swap ⟦ e′ ⟧ ⟦ e ⟧)
                                 e-∘ i-compose

composeₙ : ℕ → Expr
composeₙ zero = ` compose
composeₙ (suc n) = ` compose ∘ composeₙ n

-- TODO: Canonical forms
-- TODO: Progress
-- TODO: Preservation
-- TODO: Evaluation
