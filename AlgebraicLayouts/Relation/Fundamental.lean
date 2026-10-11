/-
  The environment relation, layers, the requirements, and the fundamental lemma.

  Checked together with Rel.lean, Mono.lean and RelSubst.lean against the repo
  at aa790de + Abs.lean, with Mathlib (Lean 4.35.0-rc4, relaxedAutoImplicit =
  false). `#print axioms Expr.fundamental`: propext, Classical.choice,
  Quot.sound. No sorry.

  `Requirements θ` collects exactly what the proof used; its fields are the
  relational form of admissibility (to be discharged per backend/layout).
-/

import Mathlib.Logic.Function.Basic
import AlgebraicLayouts.Relation.RelSubst
import AlgebraicLayouts.ExprInterp

section EnvRel

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

/-- Using a correspondence backwards. -/
theorem Corr.back {A₁ A₂ B₁ B₂ : Type 1} {h₁ : A₁ = B₁} {h₂ : A₂ = B₂}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} (c : Corr h₁ h₂ R S) {x : B₁} {y : B₂}
    (hS : S x y) : R (cast h₁.symm x) (cast h₂.symm y) := by
  subst h₁ h₂
  exact (c x y).2 hS

/-- Related environments: corresponding variables hold related values. -/
def Env.rel (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ)
    {Γ : Ctx Sig Δ} (w : W) (env₁ : Env P sigSem Γ ρ.lenv₁) (env₂ : Env P sigSem Γ ρ.lenv₂) : Prop :=
  ∀ {a : Ty Sig Δ} (x : Var Γ a), Ty.rel θ ρ a w (env₁ x) (env₂ x)

theorem Env.rel_extend {θ : RelParams P sigSem W} {Δ : LCtx} {ρ : RelEnv (P := P) (W := W) Δ}
    {Γ : Ctx Sig Δ} {w : W} {env₁ : Env P sigSem Γ ρ.lenv₁} {env₂ : Env P sigSem Γ ρ.lenv₂}
    (h : Env.rel θ ρ w env₁ env₂) {a : Ty Sig Δ} {v₁ v₂} (hv : Ty.rel θ ρ a w v₁ v₂) :
    Env.rel θ ρ w (Env.extend P sigSem env₁ v₁) (Env.extend P sigSem env₂ v₂) := by
  intro _ x
  cases x with
  | here => exact hv
  | there x => exact h x

theorem Env.rel_mono {θ : RelParams P sigSem W} (hθ : θ.Mono) {Δ : LCtx}
    {ρ : RelEnv (P := P) (W := W) Δ} (hρ : ρ.Mono) {Γ : Ctx Sig Δ} {w w' : W} (hle : w ≤ w')
    {env₁ : Env P sigSem Γ ρ.lenv₁} {env₂ : Env P sigSem Γ ρ.lenv₂}
    (h : Env.rel θ ρ w env₁ env₂) : Env.rel θ ρ w' env₁ env₂ :=
  fun x => Ty.rel_mono hθ hρ _ hle _ _ (h x)

/-- Related environments stay related under a new layout binder. -/
theorem Env.rel_weaken {θ : RelParams P sigSem W} {Δ : LCtx} {T : Adt}
    {ρ : RelEnv (P := P) (W := W) Δ} (L₁ L₂ : SemLayout P T) (R : RepRel W L₁.Rep L₂.Rep) {w : W} :
    {Γ : Ctx Sig Δ} → {env₁ : Env P sigSem Γ ρ.lenv₁} → {env₂ : Env P sigSem Γ ρ.lenv₂} →
    Env.rel θ ρ w env₁ env₂ →
    Env.rel θ (ρ.extend L₁ L₂ R) w (Env.weaken P sigSem L₁ env₁) (Env.weaken P sigSem L₂ env₂)
  | .empty, _, _, _ => fun x => nomatch x
  | .extend Γ a, env₁, env₂, h => fun x => by
      cases x with
      | here => exact (Ty.rel_weaken θ ρ L₁ L₂ R a w).back (h .here)
      | there x =>
        exact Env.rel_weaken L₁ L₂ R (Γ := Γ) (env₁ := fun y => env₁ (.there y))
          (env₂ := fun y => env₂ (.there y)) (fun y => h (.there y)) x

/-! ### Layers -/

/-- Relational lifting of a polynomial shape: `RVal` at base leaves, `Rv` at variables. -/
def PolyRel (θ : RelParams P sigSem W) {n : Nat} {E₁ E₂ : Fin n → Type 1}
    (Rv : ∀ i, W → E₁ i → E₂ i → Prop) (w : W) :
    (p : Poly n) → p.interp1 P E₁ → p.interp1 P E₂ → Prop
  | .base b, x, y => θ.RVal w b x.down y.down
  | .var i, x, y => Rv i w x y
  | .sum a b, x, y => SumRel (PolyRel θ Rv w a) (PolyRel θ Rv w b) x y
  | .prod a b, x, y => PolyRel θ Rv w a x.1 y.1 ∧ PolyRel θ Rv w b x.2 y.2

/-- Related layers, given a relation `R` between handles. -/
def LayerRel (θ : RelParams P sigSem W) {A₁ A₂ : Type} (R : RepRel W A₁ A₂) (w : W) :
    (T : Adt) → T.layer P (ULift A₁) → T.layer P (ULift A₂) → Prop
  | .plain p => PolyRel θ (fun i => i.elim0) w p
  | .mu body => PolyRel θ (fun _ w x y => R w x.down y.down) w body

/-- The relation at a view type is the relational lifting of its shape. -/
theorem Ty.rel_viewPoly (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ)
    {T : Adt} (r : LayoutRef Sig Δ T) (w : W) :
    {n : Nat} → (p : Poly n) →
    Corr (ViewPoly.interp_eq P sigSem p r ρ.lenv₁) (ViewPoly.interp_eq P sigSem p r ρ.lenv₂)
      (Ty.rel θ ρ (ViewPoly p r) w)
      (PolyRel θ (fun _ w x y => LayoutRef.rel θ ρ r w x.down y.down) w p)
  | _, .base _ => fun _ _ => Iff.rfl
  | _, .var _ => fun _ _ => Iff.rfl
  | _, .sum a b => Corr.sum _ _ (Ty.rel_viewPoly θ ρ r w a) (Ty.rel_viewPoly θ ρ r w b)
  | _, .prod a b => Corr.prod _ _ (Ty.rel_viewPoly θ ρ r w a) (Ty.rel_viewPoly θ ρ r w b)

end EnvRel

section Fundamental

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

theorem PolyRel.congr_env (θ : RelParams P sigSem W) {n : Nat} {E₁ E₁' E₂ E₂' : Fin n → Type 1}
    (e₁ : E₁ = E₁') (e₂ : E₂ = E₂') {Rv : ∀ i, W → E₁ i → E₂ i → Prop}
    {Rv' : ∀ i, W → E₁' i → E₂' i → Prop} (hR : HEq Rv Rv') (w : W) (p : Poly n) :
    Corr (congrArg (fun E => p.interp1 P E) e₁) (congrArg (fun E => p.interp1 P E) e₂)
      (PolyRel θ Rv w p) (PolyRel θ Rv' w p) := by
  subst e₁ e₂
  cases hR
  exact Corr.refl _

/-- The relation at a view type is the relation on layers. -/
theorem Ty.rel_view (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ)
    {T : Adt} (r : LayoutRef Sig Δ T) (w : W) :
    Corr (View.interp_eq P sigSem r ρ.lenv₁) (View.interp_eq P sigSem r ρ.lenv₂)
      (Ty.rel θ ρ (View T r) w) (LayerRel θ (LayoutRef.rel θ ρ r) w T) := by
  cases T with
  | mu body => exact Ty.rel_viewPoly θ ρ r w body
  | plain p =>
    exact (Ty.rel_viewPoly θ ρ r w p).trans
      (PolyRel.congr_env θ (funext fun i => i.elim0) (funext fun i => i.elim0)
        (Function.hfunext rfl fun i _ _ => i.elim0) w p)

/-- What the fundamental lemma needs from the parameters (discovered from its cases). -/
structure Requirements (θ : RelParams P sigSem W) : Prop where
  mono : θ.Mono
  related_mono : ∀ {T : Adt} {L₁ L₂ : SemLayout P T} {R : RepRel W L₁.Rep L₂.Rep},
    θ.Related L₁ L₂ R → R.Mono
  sig_related : ∀ {T : Adt} (c : Sig T), θ.Related (sigSem c) (sigSem c) (θ.sigRel c)
  rval_const : ∀ (w : W) {b : Base} (v : b.interp), θ.RVal w b (Backend.const v) (Backend.const v)
  rval_add : ∀ {w : W} {x₁ x₂ y₁ y₂}, θ.RVal w .int x₁ x₂ → θ.RVal w .int y₁ y₂ →
    θ.RVal w .int (Backend.add x₁ y₁) (Backend.add x₂ y₂)
  rval_eq : ∀ {w : W} {x₁ x₂ y₁ y₂}, θ.RVal w .int x₁ x₂ → θ.RVal w .int y₁ y₂ →
    θ.RVal w .bool (Backend.eq x₁ y₁) (Backend.eq x₂ y₂)
  cond : ∀ {w : W} {b₁ b₂ p₁ p₂ q₁ q₂}, θ.RVal w .bool b₁ b₂ → θ.RP w p₁ p₂ → θ.RP w q₁ q₂ →
    θ.RP w (Backend.cond b₁ p₁ q₁) (Backend.cond b₂ p₂ q₂)
  /-- Related layouts construct related layers into related handles. -/
  close_ : ∀ {T : Adt} {L₁ L₂ : SemLayout P T} {R : RepRel W L₁.Rep L₂.Rep},
    θ.Related L₁ L₂ R → ∀ {w : W} {u₁ u₂}, LayerRel θ R w T u₁ u₂ →
    ∀ {k₁ : L₁.Rep → P} {k₂ : L₂.Rep → P},
      (∀ w', w ≤ w' → ∀ d₁ d₂, R w' d₁ d₂ → θ.RP w' (k₁ d₁) (k₂ d₂)) →
      θ.RP w (L₁.dict.close_ u₁ k₁) (L₂.dict.close_ u₂ k₂)
  /-- Related layouts open related handles into related layers. -/
  open_ : ∀ {T : Adt} {L₁ L₂ : SemLayout P T} {R : RepRel W L₁.Rep L₂.Rep},
    θ.Related L₁ L₂ R → ∀ {w : W} {d₁ d₂}, R w d₁ d₂ →
    ∀ {k₁ : T.layer P (ULift L₁.Rep) → P} {k₂ : T.layer P (ULift L₂.Rep) → P},
      (∀ w', w ≤ w' → ∀ u₁ u₂, LayerRel θ R w' T u₁ u₂ → θ.RP w' (k₁ u₁) (k₂ u₂)) →
      θ.RP w (L₁.dict.open_ k₁ d₁) (L₂.dict.open_ k₂ d₂)

/-- Every layout variable is bound to a related pair. -/
def RelEnv.Related (θ : RelParams P sigSem W) {Δ : LCtx} (ρ : RelEnv (P := P) (W := W) Δ) : Prop :=
  ∀ {T : Adt} (l : LRef Δ T), θ.Related (ρ.lenv₁ l) (ρ.lenv₂ l) (ρ.rel l)

theorem RelEnv.Related.mono {θ : RelParams P sigSem W} (req : Requirements θ) {Δ : LCtx}
    {ρ : RelEnv (P := P) (W := W) Δ} (h : ρ.Related θ) : ρ.Mono :=
  fun l => req.related_mono (h l)

theorem RelEnv.Related.extend {θ : RelParams P sigSem W} {Δ : LCtx} {T : Adt}
    {ρ : RelEnv (P := P) (W := W) Δ} (h : ρ.Related θ) {L₁ L₂ : SemLayout P T}
    {R : RepRel W L₁.Rep L₂.Rep} (hR : θ.Related L₁ L₂ R) : (ρ.extend L₁ L₂ R).Related θ := by
  intro _ l
  cases l with
  | here => exact hR
  | there l => exact h l

theorem LayoutRef.rel_related {θ : RelParams P sigSem W} (req : Requirements θ) {Δ : LCtx}
    {ρ : RelEnv (P := P) (W := W) Δ} (h : ρ.Related θ) {T : Adt} (r : LayoutRef Sig Δ T) :
    θ.Related (r.interp P sigSem ρ.lenv₁) (r.interp P sigSem ρ.lenv₂) (LayoutRef.rel θ ρ r) := by
  cases r with
  | var l => exact h l
  | concrete c => exact req.sig_related c

/-! ### CPS helpers -/

theorem CompRel.ret {θ : RelParams P sigSem W} {A₁ A₂ : Type 1} {S : W → A₁ → A₂ → Prop}
    (hS : ∀ w w' x y, w ≤ w' → S w x y → S w' x y) {w : W} {v₁ : A₁} {v₂ : A₂}
    (h : S w v₁ v₂) : CompRel θ S w (Comp.ret P v₁) (Comp.ret P v₂) :=
  fun w' hle _ _ hκ => hκ w' le_rfl _ _ (hS _ _ _ _ hle h)

theorem CompRel.bind {θ : RelParams P sigSem W} {A₁ A₂ B₁ B₂ : Type 1}
    {S : W → A₁ → A₂ → Prop} {S' : W → B₁ → B₂ → Prop} {w : W}
    {m₁ : Comp P A₁} {m₂ : Comp P A₂} {f₁ : A₁ → Comp P B₁} {f₂ : A₂ → Comp P B₂}
    (hm : CompRel θ S w m₁ m₂)
    (hf : ∀ w', w ≤ w' → ∀ a₁ a₂, S w' a₁ a₂ → CompRel θ S' w' (f₁ a₁) (f₂ a₂)) :
    CompRel θ S' w (Comp.bind P m₁ f₁) (Comp.bind P m₂ f₂) :=
  fun w' hle κ₁ κ₂ hκ => hm w' hle _ _ fun w'' hle' a₁ a₂ ha =>
    hf w'' (le_trans hle hle') a₁ a₂ ha w'' le_rfl κ₁ κ₂
      fun w''' hle'' => hκ w''' (le_trans hle' hle'')

/-! ### The fundamental lemma -/

/-- **The fundamental lemma**: every expression is related to itself, in related
environments, for related layouts. -/
theorem Expr.fundamental (θ : RelParams P sigSem W) (req : Requirements θ) :
    {Δ : LCtx} → {Γ : Ctx Sig Δ} → {a : Ty Sig Δ} → (e : Expr Γ a) →
    (ρ : RelEnv (P := P) (W := W) Δ) → ρ.Related θ → (w : W) →
    (env₁ : Env P sigSem Γ ρ.lenv₁) → (env₂ : Env P sigSem Γ ρ.lenv₂) →
    Env.rel θ ρ w env₁ env₂ →
    CompRel θ (Ty.rel θ ρ a) w (Expr.interp P sigSem e ρ.lenv₁ env₁)
      (Expr.interp P sigSem e ρ.lenv₂ env₂)
  | _, _, a, .var x, ρ, hρ, _, _, _, henv =>
      CompRel.ret (S := Ty.rel θ ρ a)
        (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h) (henv x)
  | _, _, _, .lit (b := b) v, ρ, hρ, w, _, _, _ =>
      CompRel.ret (S := Ty.rel θ ρ (.base b))
        (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h) (req.rval_const w v)
  | _, _, _, .lam (a := a) (b := b) e, ρ, hρ, _, _, _, henv =>
      CompRel.ret (S := Ty.rel θ ρ (.arr a b))
        (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h)
        (fun w' hle x y hxy => Expr.fundamental θ req e ρ hρ w' _ _
          (Env.rel_extend (Env.rel_mono req.mono (hρ.mono req) hle henv) hxy))
  | _, _, _, .app e₁ e₂, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w' hle f g hfg =>
        CompRel.bind (Expr.fundamental θ req e₂ ρ hρ w' env₁ env₂
            (Env.rel_mono req.mono (hρ.mono req) hle henv)) fun w'' hle' x y hxy =>
          hfg w'' hle' x y hxy
  | _, _, _, .toRef e, ρ, hρ, w, env₁, env₂, henv =>
      Expr.fundamental θ req e ρ hρ w env₁ env₂ henv
  | _, _, _, .inl (a := a) (b := b) e, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e ρ hρ w env₁ env₂ henv) fun _ _ x y hxy =>
        CompRel.ret (S := Ty.rel θ ρ (.sum a b))
          (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h) (v₁ := .inl x)
          (v₂ := .inl y) hxy
  | _, _, _, .inr (a := a) (b := b) e, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e ρ hρ w env₁ env₂ henv) fun _ _ x y hxy =>
        CompRel.ret (S := Ty.rel θ ρ (.sum a b))
          (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h) (v₁ := .inr x)
          (v₂ := .inr y) hxy
  | _, _, _, .pair (a := a) (b := b) e₁ e₂, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w' hle x₁ x₂ hx =>
        CompRel.bind (Expr.fundamental θ req e₂ ρ hρ w' env₁ env₂
            (Env.rel_mono req.mono (hρ.mono req) hle henv)) fun w'' hle' y₁ y₂ hy =>
          CompRel.ret (S := Ty.rel θ ρ (.prod a b))
            (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h)
            (v₁ := (x₁, y₁)) (v₂ := (x₂, y₂))
            ⟨Ty.rel_mono req.mono (hρ.mono req) _ hle' _ _ hx, hy⟩
  | _, _, _, .matchPair e₁ e₂, ρ, hρ, w, env₁, env₂, henv => by
      refine CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) ?_
      intro w' hle p q hpq
      obtain ⟨x₁, y₁⟩ := p
      obtain ⟨x₂, y₂⟩ := q
      exact Expr.fundamental θ req e₂ ρ hρ w' _ _
        (Env.rel_extend (Env.rel_extend (Env.rel_mono req.mono (hρ.mono req) hle henv) hpq.1) hpq.2)
  | _, _, _, .matchSum e₁ e₂ e₃, ρ, hρ, w, env₁, env₂, henv => by
      refine CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) ?_
      intro w' hle p q hpq
      rcases p with x₁ | y₁ <;> rcases q with x₂ | y₂
      · exact Expr.fundamental θ req e₂ ρ hρ w' _ _
          (Env.rel_extend (Env.rel_mono req.mono (hρ.mono req) hle henv)
            (show Ty.rel θ ρ _ w' x₁ x₂ from hpq))
      · exact hpq.elim
      · exact hpq.elim
      · exact Expr.fundamental θ req e₃ ρ hρ w' _ _
          (Env.rel_extend (Env.rel_mono req.mono (hρ.mono req) hle henv)
            (show Ty.rel θ ρ _ w' y₁ y₂ from hpq))
  | _, _, _, .add e₁ e₂, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w' hle x₁ x₂ hx =>
        CompRel.bind (Expr.fundamental θ req e₂ ρ hρ w' env₁ env₂
            (Env.rel_mono req.mono (hρ.mono req) hle henv)) fun w'' hle' y₁ y₂ hy =>
          CompRel.ret (S := Ty.rel θ ρ (.base .int))
            (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h)
            (req.rval_add (req.mono.rval hle' hx) hy)
  | _, _, _, .eq e₁ e₂, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w' hle x₁ x₂ hx =>
        CompRel.bind (Expr.fundamental θ req e₂ ρ hρ w' env₁ env₂
            (Env.rel_mono req.mono (hρ.mono req) hle henv)) fun w'' hle' y₁ y₂ hy =>
          CompRel.ret (S := Ty.rel θ ρ (.base .bool))
            (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h)
            (req.rval_eq (req.mono.rval hle' hx) hy)
  | _, _, _, .ite e₁ e₂ e₃, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w' hle b₁ b₂ hb =>
        fun w'' hle' κ₁ κ₂ hκ =>
          have henv' : Env.rel θ ρ w' env₁ env₂ := Env.rel_mono req.mono (hρ.mono req) hle henv
          req.cond (req.mono.rval hle' hb)
            (Expr.fundamental θ req e₂ ρ hρ w' env₁ env₂ henv' w'' hle' κ₁ κ₂ hκ)
            (Expr.fundamental θ req e₃ ρ hρ w' env₁ env₂ henv' w'' hle' κ₁ κ₂ hκ)
  | _, _, _, .layoutLam (T := T) (body := body) e, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.ret (S := Ty.rel θ ρ (.forallLayout T body))
        (fun _ _ _ _ hle h => Ty.rel_mono req.mono (hρ.mono req) _ hle _ _ h)
        (fun L₁ L₂ R hR => Expr.fundamental θ req e (ρ.extend L₁ L₂ R) (hρ.extend hR) w _ _
          (Env.rel_weaken L₁ L₂ R henv))
  | _, _, _, .layoutApp (T := T) (body := body) e L, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e ρ hρ w env₁ env₂ henv) fun w' _ f g hfg =>
        (CompRel.congr (θ := θ) (fun w => Ty.rel_instantiate θ ρ body L w) w'
          (congrArg (Comp P) (Ty.interp_instantiate P sigSem ρ.lenv₁ body L))
          (congrArg (Comp P) (Ty.interp_instantiate P sigSem ρ.lenv₂ body L))).back
          (hfg _ _ _ (LayoutRef.rel_related req hρ L))
  | _, _, _, .open_ (r := r) e₁ e₂ _, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e₁ ρ hρ w env₁ env₂ henv) fun w₁ hle₁ h₁ h₂ hh =>
        fun w₂ hle₂ κ₁ κ₂ hκ =>
          req.open_ (LayoutRef.rel_related req hρ r)
            (LayoutRef.rel_mono req.mono (hρ.mono req) r hle₂ hh)
            fun w₃ hle₃ u₁ u₂ hu =>
              Expr.fundamental θ req e₂ ρ hρ w₃ _ _
                (Env.rel_extend
                  (Env.rel_mono req.mono (hρ.mono req) (le_trans hle₁ (le_trans hle₂ hle₃)) henv)
                  ((Ty.rel_view θ ρ r w₃).back hu))
                w₃ le_rfl κ₁ κ₂ fun w₄ hle₄ => hκ w₄ (le_trans hle₃ hle₄)
  | _, _, _, .close (r := r) e, ρ, hρ, w, env₁, env₂, henv =>
      CompRel.bind (Expr.fundamental θ req e ρ hρ w env₁ env₂ henv) fun _ _ v₁ v₂ hv =>
        fun w₂ hle₂ κ₁ κ₂ hκ =>
          req.close_ (LayoutRef.rel_related req hρ r)
            ((Ty.rel_view θ ρ r w₂ _ _).1 (Ty.rel_mono req.mono (hρ.mono req) _ hle₂ _ _ hv))
            fun w₃ hle₃ d₁ d₂ hd => hκ w₃ hle₃ ⟨d₁⟩ ⟨d₂⟩ hd

end Fundamental
