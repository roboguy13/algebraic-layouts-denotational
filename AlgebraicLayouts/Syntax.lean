inductive Base : Type where
| int : Base
| bool : Base
| unit : Base

inductive Poly : Nat → Type where
| base (b : Base) : Poly n
| var (i : Fin n) : Poly n
| sum (a b : Poly n) : Poly n
| prod (a b : Poly n) : Poly n

inductive Adt : Type where
| plain (p : Poly 0) : Adt
| mu (body : Poly 1) : Adt

-- Layout contexts
inductive LCtx : Type where
| empty : LCtx
| extend (Δ : LCtx) (T : Adt)

inductive LRef : LCtx → Adt → Type where
| here : ∀ {Δ : LCtx} {T}, LRef (Δ.extend T) T
| there : ∀ {Δ : LCtx} {T1 T2}, LRef Δ T1 → LRef (Δ.extend T2) T1

inductive LayoutRef (Sig : Adt → Type) : LCtx → Adt → Type where
| var {Δ T} (l : LRef Δ T) : LayoutRef Sig Δ T
| concrete {Δ T} (c : Sig T) : LayoutRef Sig Δ T

inductive Ty (Sig : Adt → Type) : LCtx → Type where
| base (b : Base) : Ty Sig Δ
| atL (T : Adt) (l : LayoutRef Sig Δ T) : Ty Sig Δ  -- T@l
| ref (T : Adt) (l : LayoutRef Sig Δ T) : Ty Sig Δ -- opaque REF inside a view
| sum (a b : Ty Sig Δ) : Ty Sig Δ
| prod (a b : Ty Sig Δ) : Ty Sig Δ
| arr (a b : Ty Sig Δ) : Ty Sig Δ
| forallLayout (T : Adt) (body : Ty Sig (Δ.extend T)) : Ty Sig Δ

inductive Ctx (Sig : Adt → Type) (Δ : LCtx) : Type where
| empty : Ctx Sig Δ
| extend (Γ : Ctx Sig Δ) (a : Ty Sig Δ)

inductive Var {Sig : Adt → Type} {Δ} : Ctx Sig Δ → Ty Sig Δ → Type where
| here : ∀ {Γ : Ctx Sig Δ} {a : Ty Sig Δ}, Var (Γ.extend a) a
| there : ∀ {Γ : Ctx Sig Δ} {a b : Ty Sig Δ}, Var Γ a → Var (Γ.extend b) a

variable {Sig : Adt → Type}

/-! ## Renaming of layout variables -/

/-- A renaming of layout variables from `Δ` to `Δ'`. -/
abbrev LRen (Δ Δ' : LCtx) : Type := ∀ {T : Adt}, LRef Δ T → LRef Δ' T

/-- Extend a renaming under a binder. -/
def LRen.lift {Δ Δ' : LCtx} {T : Adt} (ρ : LRen Δ Δ') : LRen (Δ.extend T) (Δ'.extend T)
  | _, .here => .here
  | _, .there l => .there (ρ l)

def LayoutRef.rename {Δ Δ' : LCtx} {T : Adt} (ρ : LRen Δ Δ') :
    LayoutRef Sig Δ T → LayoutRef Sig Δ' T
  | .var l => .var (ρ l)
  | .concrete c => .concrete c

def Ty.rename {Δ Δ' : LCtx} (ρ : LRen Δ Δ') : Ty Sig Δ → Ty Sig Δ'
  | .base b => .base b
  | .atL T l => atL T (l.rename ρ)
  | .ref T l => .ref T (l.rename ρ)
  | .sum a b => .sum (a.rename ρ) (b.rename ρ)
  | .prod a b => .prod (a.rename ρ) (b.rename ρ)
  | .arr a b => .arr (a.rename ρ) (b.rename ρ)
  | .forallLayout T body => .forallLayout T (body.rename ρ.lift)

/-- Weaken a type under one new layout binder. -/
def Ty.weaken {Δ : LCtx} {T : Adt} (a : Ty Sig Δ) : Ty Sig (Δ.extend T) :=
  a.rename (fun l => .there l)

/-! ## Substitution of layout references for layout variables -/

/-- A substitution of layout references for the layout variables of `Δ`. -/
abbrev LSubst (Sig : Adt → Type) (Δ Δ' : LCtx) : Type :=
  ∀ {T : Adt}, LRef Δ T → LayoutRef Sig Δ' T

/-- Extend a substitution under a binder. -/
def LSubst.lift {Δ Δ' : LCtx} {T : Adt} (σ : LSubst Sig Δ Δ') :
    LSubst Sig (Δ.extend T) (Δ'.extend T)
  | _, .here => .var .here
  | _, .there l => (σ l).rename (fun l' => .there l')

/-- Substitute `L` for the innermost layout variable. -/
def LSubst.single {Δ : LCtx} {T : Adt} (L : LayoutRef Sig Δ T) :
    LSubst Sig (Δ.extend T) Δ
  | _, .here => L
  | _, .there l => .var l

def LayoutRef.subst {Δ Δ' : LCtx} {T : Adt} (σ : LSubst Sig Δ Δ') :
    LayoutRef Sig Δ T → LayoutRef Sig Δ' T
  | .var l => σ l
  | .concrete c => .concrete c

def Ty.subst {Δ Δ' : LCtx} (σ : LSubst Sig Δ Δ') : Ty Sig Δ → Ty Sig Δ'
  | .base b => .base b
  | .atL T l => atL T (l.subst σ)
  | .ref T l => .ref T (l.subst σ)
  | .sum a b => .sum (a.subst σ) (b.subst σ)
  | .prod a b => .prod (a.subst σ) (b.subst σ)
  | .arr a b => .arr (a.subst σ) (b.subst σ)
  | .forallLayout T body => .forallLayout T (body.subst σ.lift)

/-- The result type of layout application: `body[ℓ := L]`. -/
def Ty.instantiate {Δ : LCtx} {T : Adt} (body : Ty Sig (Δ.extend T))
    (L : LayoutRef Sig Δ T) : Ty Sig Δ :=
  body.subst (LSubst.single L)

/-! ## Mapping over term contexts -/

def Ctx.map {Δ Δ' : LCtx} (f : Ty Sig Δ → Ty Sig Δ') : Ctx Sig Δ → Ctx Sig Δ'
  | .empty => .empty
  | .extend Γ a => .extend (Γ.map f) (f a)

/-- Weaken every type in a context under one new layout binder
(used by `∀Layout` introduction). -/
def Ctx.weaken {Δ : LCtx} {T : Adt} (Γ : Ctx Sig Δ) : Ctx Sig (Δ.extend T) :=
  Γ.map Ty.weaken

/-- Variables survive mapping a context. -/
def Var.map {Δ Δ' : LCtx} (f : Ty Sig Δ → Ty Sig Δ') {Γ : Ctx Sig Δ} {a : Ty Sig Δ} :
    Var Γ a → Var (Γ.map f) (f a)
  | .here => .here
  | .there x => .there (x.map f)

-- Replace all var occurrences with r
def ViewPoly (p : Poly n) (r : LayoutRef Sig Δ T) : Ty Sig Δ :=
  match p with
  | .base b => .base b
  | .var _ => .ref T r
  | .sum a b => .sum (ViewPoly a r) (ViewPoly b r)
  | .prod a b => .prod (ViewPoly a r) (ViewPoly b r)

def View (T : Adt) (r : LayoutRef Sig Δ T) : Ty Sig Δ :=
  match T with
  | .plain p => ViewPoly p r
  | .mu p => ViewPoly p r

inductive Stable : Ty Sig Δ → Prop where
| base : ∀ {b}, Stable (.base b)
| atL : ∀ {T l}, Stable (.atL T l)
| arr : ∀ {a b}, Stable a → Stable b → Stable (.arr a b)
| forallLayout : ∀ {body}, Stable body → Stable (.forallLayout T body)

omit Sig in
abbrev Base.interp : Base → Type
| .bool => Bool
| .int => Int
| .unit => Unit

omit Sig in
inductive Expr {Sig : Adt → Type} : ∀ {Δ : LCtx}, Ctx Sig Δ → Ty Sig Δ → Type where
| var (x : Var Γ a) : Expr Γ a
| lit {Γ} {b : Base} (v : b.interp) : Expr Γ (.base b)
| lam {Γ a b} (e : Expr (Γ.extend a) b) : Expr Γ (.arr a b)
| app {Γ a b} (e1 : Expr Γ (.arr a b)) (e2 : Expr Γ a) : Expr Γ b

| layoutLam {Δ : LCtx} {Γ : Ctx Sig Δ} {T : Adt} {body : Ty Sig (Δ.extend T)}
    (e : Expr (Γ.weaken (T := T)) body) : Expr Γ (.forallLayout T body)
| layoutApp {Δ : LCtx} {Γ : Ctx Sig Δ} {T : Adt} {body : Ty Sig (Δ.extend T)}
    (e : Expr Γ (.forallLayout T body)) (L : LayoutRef Sig Δ T) : Expr Γ (body.instantiate L)

| open_ : Expr Γ (.atL T r) → Expr (Γ.extend (View T r)) τ → Stable τ → Expr Γ τ
| close : Expr Γ (View T r) → Expr Γ (.atL T r)

| inl {a b} (e : Expr Γ a) : Expr Γ (.sum a b)
| inr {a b} (e : Expr Γ b) : Expr Γ (.sum a b)
| pair (e1 : Expr Γ a) (e2 : Expr Γ b) : Expr Γ (.prod a b)
| matchPair {a b r} (e1 : Expr Γ (.prod a b)) (e2 : Expr ((Γ.extend a).extend b) r) : Expr Γ r
| matchSum {a b r} (e1 : Expr Γ (.sum a b)) (e2 : Expr (Γ.extend a) r) (e3 : Expr (Γ.extend b) r) : Expr Γ r

| add {Γ} (e1 : Expr Γ (.base .int)) (e2 : Expr Γ (.base .int)) : Expr Γ (.base .int)
| eq {Γ} (e1 : Expr Γ (.base .int)) (e2 : Expr Γ (.base .int)) : Expr Γ (.base .bool)
| ite {Γ} {a} (e1 : Expr Γ (.base .bool)) (e2 : Expr Γ a) (e3 : Expr Γ a) : Expr Γ a
