import AlgebraicLayouts.Syntax
import AlgebraicLayouts.TyInterp

variable {Sig : Adt → Type}
variable (P : Type) [Backend P]
variable (sigSem : ∀ {T : Adt}, Sig T → SemLayout P T)

abbrev Env {Δ} (Γ : Ctx Sig Δ) (lenv : LEnv P Δ) :=
  ∀ {a},
  Var Γ a → a.interp P sigSem lenv

def Env.extend {Δ} {Γ} {lenv : LEnv P Δ} {a : Ty Sig Δ} (env : Env P sigSem Γ lenv) (v : a.interp P sigSem lenv) :
    Env P sigSem (Γ.extend a) lenv :=
  fun x =>
  match x with
  | .here => v
  | .there x' => env x'

omit [Backend P] in
/-- Move an environment under a new layout binder (used by `layoutLam`). -/
def Env.weaken {Δ : LCtx} {T : Adt} {lenv : LEnv P Δ} (L : SemLayout P T) :
    {Γ : Ctx Sig Δ} → Env P sigSem Γ lenv → Env P sigSem (Γ.weaken (T := T)) (lenv.extend P L)
| .empty, _ => fun x => nomatch x
| .extend _ a, env => fun x =>
    match x with
    | .here => cast (Ty.interp_weaken P sigSem lenv L a).symm (env .here)
    | .there x' => Env.weaken L (fun y => env (.there y)) x'

/-! ## The CPS monad -/
def Comp.ret {B : Type 1} (v : B) : Comp P B := fun κ => κ v

def Comp.bind {A B : Type 1} (m : Comp P A) (f : A → Comp P B) : Comp P B :=
  fun κ => m (fun a => f a κ)

/-! ## Expressions -/
def Expr.interp {Δ} {Γ : Ctx Sig Δ} {a : Ty Sig Δ}  :
    Expr Γ a → (lenv : LEnv P Δ) → Env P sigSem Γ lenv → Comp P (a.interp P sigSem lenv)
| .lit (b := b) v, lenv, env => Comp.ret P ⟨Backend.const v⟩
| .var x, lenv, env => Comp.ret P (env x)
| .lam e, lenv, env => Comp.ret P (fun x => e.interp lenv (env.extend _ _ x))
| .app e1 e2, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun f =>
    Comp.bind P (e2.interp lenv env) fun x =>
    f x
| .inl e, lenv, env => Comp.bind P (e.interp lenv env) fun x => Comp.ret P (.inl x)
| .inr e, lenv, env => Comp.bind P (e.interp lenv env) fun x => Comp.ret P (.inr x)
| .pair e1 e2, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun x =>
    Comp.bind P (e2.interp lenv env) fun y =>
    Comp.ret P (x, y)
| .matchPair e1 e2, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun v =>
    match v with
    | (x, y) =>
      e2.interp lenv (Env.extend P sigSem (Env.extend P sigSem env x) y)
| .matchSum e1 e2 e3, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun v =>
    match v with
    | .inl x => e2.interp lenv (Env.extend P sigSem env x)
    | .inr y => e3.interp lenv (Env.extend P sigSem env y)
| .add e1 e2, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun x =>
    Comp.bind P (e2.interp lenv env) fun y =>
    Comp.ret P ⟨Backend.add x.down y.down⟩
| .eq e1 e2, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun x =>
    Comp.bind P (e2.interp lenv env) fun y =>
    Comp.ret P ⟨Backend.eq x.down y.down⟩
| .ite e1 e2 e3, lenv, env =>
    Comp.bind P (e1.interp lenv env) fun b => fun κ =>
      ⟨Backend.cond b.down (e2.interp lenv env κ).down (e3.interp lenv env κ).down⟩

| .layoutLam e, lenv, env =>
    Comp.ret P (fun L => e.interp (lenv.extend P L) (Env.weaken P sigSem L env))

| .layoutApp (body := body) e L, lenv, env =>
    Comp.bind P (e.interp lenv env) fun f =>
    cast (congrArg (Comp P) (Ty.interp_instantiate P sigSem lenv body L).symm) (f (L.interp P sigSem lenv))

| .open_ (r := r) e₁ e₂ _, lenv, env =>
    Comp.bind P (e₁.interp lenv env) fun h => fun κ =>
      ⟨(r.interp P sigSem lenv).dict.open_
        (fun layer =>
          (e₂.interp lenv
            (Env.extend P sigSem env (cast (View.interp_eq P sigSem r lenv).symm layer)) κ).down)
        h.down⟩

| .close (r := r) e, lenv, env =>
    Comp.bind P (e.interp lenv env) fun layer => fun κ =>
      let L := r.interp P sigSem lenv
      ⟨L.dict.fresh fun dest =>
        Backend.op (L.dict.put (cast (View.interp_eq P sigSem r lenv) layer) dest)
          (κ ⟨dest⟩).down⟩

| .toRef e, lenv, env => e.interp lenv env
