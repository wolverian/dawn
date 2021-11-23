data Int : Set where
  swap : Int
  clone : Int
  drop : Int
  quot : Int
  compose : Int
  apply : Int

infix 5 ⟦_⟧
infixl 7 _∘_
infix 9 `_

data Expr : Set where

  `_ : Int → Expr

  ⟦_⟧ : Expr → Expr

  _∘_ : Expr → Expr → Expr

data Value : Expr → Set where

  ⟦_⟧ : (e : Expr) → Value ⟦ e ⟧

infixl 4 _,_

data Stack : Set where

  ⟨⟩ : Stack

  _,_ : ∀ {e}
      → (V : Stack)
      → (v : Value e)
      → Stack

infix 3 ⟪_⟫_⟶⟪_⟫


data ⟪_⟫_⟶⟪_⟫ : Stack → Expr → Stack → Set where

  ξ-i-swap : ∀ {V e e′}
           → (v : Value e)
           → (v′ : Value e′)
             ---------------------------------------
           → ⟪ (V , v) , v′ ⟫ ` swap ⟶⟪ V , v′ , v ⟫

  ξ-i-clone : ∀ {V e}
            → (v : Value e)
              --------------------------------
            → ⟪ V , v ⟫ ` clone ⟶⟪ V , v , v ⟫

  ξ-i-drop : ∀ {V e}
           → (v : Value e)
             --------------------------------
           → ⟪ V , v ⟫ ` drop ⟶⟪ V ⟫

  ξ-i-quote : ∀ {V e}
            → (v : Value e)
              -------------------------------
            → ⟪ V , v ⟫ ` quot ⟶⟪ V , ⟦ e ⟧ ⟫

  ξ-i-compose : ∀ {V e e′}
                ---------------------------------------------------
              → ⟪ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟫ ` compose ⟶⟪ V , ⟦ e ∘ e′ ⟧ ⟫

  ξ-i-apply : ∀ {V V′ e}
            → ⟪ V ⟫ e ⟶⟪ V′ ⟫
              -----------------------------
            → ⟪ V , ⟦ e ⟧ ⟫ ` apply ⟶⟪ V′ ⟫

  ξ-quote : ∀ {V e}
            --------------------------
          → ⟪ V ⟫ ⟦ e ⟧ ⟶⟪ V , ⟦ e ⟧ ⟫

  ξ-∘ : ∀ {V V′ W v v′}
      → ⟪ V  ⟫ v  ⟶⟪ V′ ⟫
      → ⟪ V′ ⟫ v′ ⟶⟪ W  ⟫
        -------------------
      → ⟪ V ⟫ v ∘ v′ ⟶⟪ W ⟫

false : Expr
false = ⟦ ` drop ⟧

false-value : Value false
false-value = ⟦ ` drop ⟧

true : Expr
true = ⟦ ` swap ∘ ` drop ⟧

true-value : Value true
true-value = ⟦ ` swap ∘ ` drop ⟧

false-thm : ∀ {V e e′}
          → (v : Value e)
          → (v′ : Value e′)
            -----------------------------------------
          → ⟪ V , v , v′ ⟫ false ∘ ` apply ⟶⟪ V , v ⟫
false-thm {V} {e} {e′} _ v′ = ξ-∘ ξ-quote (ξ-i-apply (ξ-i-drop v′))

true-thm : ∀ {V e e′}
         → (v : Value e)
         → (v′ : Value e′)
           -----------------------------------------
         → ⟪ V , v , v′ ⟫ true ∘ ` apply ⟶⟪ V , v′ ⟫
true-thm {V} {e} {e′} v v′ = ξ-∘ ξ-quote (ξ-i-apply (ξ-∘ (ξ-i-swap v v′) (ξ-i-drop v)))

or : Expr
or = ` clone ∘ ` apply

or-false-false : ∀ {V e}
               → (v : Value e)
                 -------------------------------------
               → ⟪ V , v , false-value ⟫ or ⟶⟪ V , v ⟫
or-false-false {V} {e} v = ξ-∘ (ξ-i-clone false-value) (ξ-i-apply (ξ-i-drop false-value))

or-true : ∀ {V e}
        → (v : Value e)
          ---------------------------------------------
        → ⟪ V , v , true-value ⟫ or ⟶⟪ V , true-value ⟫
or-true {V} {e} v = ξ-∘ (ξ-i-clone true-value) (ξ-i-apply (ξ-∘ (ξ-i-swap v true-value) (ξ-i-drop v)))
