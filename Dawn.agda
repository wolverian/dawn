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

  [_] : (e : Expr) → Value [ e ]

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
             ---------------------------
           → ⟨ V , [ e ] ⟩ ` drop →⟨ V ⟩

  i-quote : ∀ {V e}
              -----------------------------------
            → ⟨ V , [ e ] ⟩ ` quot →⟨ V , [ e ] ⟩

  i-compose : ∀ {V e e′}
                ---------------------------------------------------
              → ⟨ V , [ e ] , [ e′ ] ⟩ ` compose →⟨ V , [ e ∘ e′ ] ⟩

  i-apply : ∀ {V V′ e}
            → ⟨ V ⟩ e →⟨ V′ ⟩
              -----------------------------
            → ⟨ V , [ e ] ⟩ ` apply →⟨ V′ ⟩

  e-quote : ∀ {V e}
            --------------------------
          → ⟨ V ⟩ [ e ] →⟨ V , [ e ] ⟩

  e-∘ : ∀ {V V′ W v v′}
      → ⟨ V  ⟩ v  →⟨ V′ ⟩
      → ⟨ V′ ⟩ v′ →⟨ W  ⟩
        -------------------
      → ⟨ V ⟩ v ∘ v′ →⟨ W ⟩

⊥ : Expr
⊥ = [ ` drop ]

⊥-value : Value ⊥
⊥-value = [ ` drop ]

⊤ : Expr
⊤ = [ ` swap ∘ ` drop ]

⊤-value : Value ⊤
⊤-value = [ ` swap ∘ ` drop ]

⊥-thm : ∀ {V e e′} → ⟨ V , [ e ] , [ e′ ] ⟩ ⊥ ∘ ` apply →⟨ V , [ e ] ⟩
⊥-thm {V} {e} {e′} = e-∘ e-quote (i-apply i-drop)

⊤-thm : ∀ {V e e′} → ⟨ V , [ e ] , [ e′ ] ⟩ ⊤ ∘ ` apply →⟨ V , [ e′ ] ⟩
⊤-thm {V} {e} {e′} = e-∘ e-quote (i-apply (e-∘ (i-swap [ e ] [ e′ ]) i-drop))

∨ : Expr
∨ = ` clone ∘ ` apply

∨-⊥-⊥ : ∀ {V e} → ⟨ V , [ e ] , ⊥-value ⟩ ∨ →⟨ V , [ e ] ⟩
∨-⊥-⊥ {V} {e} = e-∘ (i-clone ⊥-value) (i-apply i-drop)

∨-⊤ : ∀ {V e} → ⟨ V , [ e ] , ⊤-value ⟩ ∨ →⟨ V , ⊤-value ⟩
∨-⊤ {V} {e} = e-∘ (i-clone ⊤-value) (i-apply (e-∘ (i-swap [ e ] ⊤-value) i-drop))

quoteₙ : ℕ → Expr
quoteₙ zero = ` quot
quoteₙ (suc n) = quoteₙ n ∘ ` swap ∘ ` quot ∘ ` swap ∘ ` compose

quote₂-thm : ∀ {V e e′} → ⟨ V , [ e ] , [ e′ ] ⟩ quoteₙ 1 →⟨ V , [ e ∘ e′ ] ⟩
quote₂-thm {V} {e} {e′} = e-∘
                            (e-∘ (e-∘ (e-∘ i-quote (i-swap [ e ] [ e′ ])) i-quote)
                             (i-swap [ e′ ] [ e ]))
                            i-compose

composeₙ : ℕ → Expr
composeₙ zero = ` compose
composeₙ (suc n) = ` compose ∘ composeₙ n
