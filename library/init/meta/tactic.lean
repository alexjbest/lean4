/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.function init.data.option.basic init.util
import init.category.combinators init.category.monad init.category.alternative init.category.monad_fail
import init.data.nat.div init.meta.exceptional init.meta.format init.meta.environment
import init.meta.pexpr init.data.to_string init.data.string.basic
meta constant tactic_state : Type

universes u v

namespace tactic_state
meta constant env         : tactic_state → environment
meta constant to_format   : tactic_state → format
/- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
meta constant format_expr : tactic_state → expr → format
meta constant get_options : tactic_state → options
meta constant set_options : tactic_state → options → tactic_state
end tactic_state

meta instance : has_to_format tactic_state :=
⟨tactic_state.to_format⟩

meta inductive tactic_result (α : Type u)
| success      : α → tactic_state → tactic_result
| exception {} : option (unit → format) → option expr → tactic_state → tactic_result

open tactic_result

section
variables {α : Type u}
variables [has_to_string α]

meta def tactic_result_to_string : tactic_result α → string
| (success a s)              := to_string a
| (exception (some t) ref s) := "Exception: " ++ to_string (t ())
| (exception none ref s)     := "[silent exception]"

meta instance : has_to_string (tactic_result α) :=
⟨tactic_result_to_string⟩
end

attribute [reducible]
meta def tactic (α : Type u) :=
tactic_state → tactic_result α

section
variables {α : Type u} {β : Type v}

@[inline] meta def tactic_fmap (f : α → β) (t : tactic α) : tactic β :=
λ s, tactic_result.cases_on (t s)
  (λ a s', success (f a) s')
  (λ e s', exception e s')

@[inline] meta def tactic_bind (t₁ : tactic α) (t₂ : α → tactic β) : tactic β :=
λ s,  tactic_result.cases_on (t₁ s)
  (λ a s', t₂ a s')
  (λ e s', exception e s')

@[inline] meta def tactic_return (a : α) : tactic α :=
λ s, success a s

meta def tactic_orelse {α : Type u} (t₁ t₂ : tactic α) : tactic α :=
λ s, tactic_result.cases_on (t₁ s)
  success
  (λ e₁ ref₁ s', tactic_result.cases_on (t₂ s)
     success
     exception)

@[inline] meta def tactic_seq (t₁ : tactic α) (t₂ : tactic β) : tactic β :=
tactic_bind t₁ (λ a, t₂)

infixl ` >>=[tactic] `:2 := tactic_bind
infixl ` >>[tactic] `:2  := tactic_seq
end

meta instance : monad tactic :=
{map := @tactic_fmap, ret := @tactic_return, bind := @tactic_bind}

meta def tactic.mk_exception {α : Type u} {β : Type v} [has_to_format β] (msg : β) (ref : option expr) (s : tactic_state) : tactic_result α :=
exception (some (λ _, to_fmt msg)) none s

meta def tactic.fail {α : Type u} {β : Type v} [has_to_format β] (msg : β) : tactic α :=
λ s, tactic.mk_exception msg none s

meta def tactic.silent_fail {α : Type u} : tactic α :=
λ s, exception none none s

meta def tactic.failed {α : Type u} : tactic α :=
tactic.fail "failed"

meta instance : monad_fail tactic :=
{ tactic.monad with fail := λ α s, tactic.fail (to_fmt s) }

meta instance : alternative tactic :=
⟨@tactic_fmap, (λ α a s, success a s), (@fapp _ _), @tactic.failed, @tactic_orelse⟩

meta def {u₁ u₂} tactic.up {α : Type u₂} (t : tactic α) : tactic (ulift.{u₁} α) :=
λ s, match t s with
| success a s'      := success (ulift.up a) s'
| exception t ref s := exception t ref s
end

meta def {u₁ u₂} tactic.down {α : Type u₂} (t : tactic (ulift.{u₁} α)) : tactic α :=
λ s, match t s with
| success (ulift.up a) s' := success a s'
| exception t ref s       := exception t ref s
end

namespace tactic
variables {α : Type u}

meta def try_core (t : tactic α) : tactic (option α) :=
λ s, tactic_result.cases_on (t s)
 (λ a, success (some a))
 (λ e ref s', success none s)

meta def skip : tactic unit :=
success ()

meta def try (t : tactic α) : tactic unit :=
try_core t >>[tactic] skip

meta def fail_if_success {α : Type u} (t : tactic α) : tactic unit :=
λ s, tactic_result.cases_on (t s)
 (λ a s, mk_exception "fail_if_success combinator failed, given tactic succeeded" none s)
 (λ e ref s', success () s)

open nat
/- (repeat_at_most n t): repeat the given tactic at most n times or until t fails -/
meta def repeat_at_most : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := (do t, repeat_at_most n t) <|> skip

/- (repeat_exactly n t) : execute t n times -/
meta def repeat_exactly : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := do t, repeat_exactly n t

meta def repeat : tactic unit → tactic unit :=
repeat_at_most 100000

meta def returnopt (e : option α) : tactic α :=
λ s, match e with
| (some a) := success a s
| none     := mk_exception "failed" none s
end

meta instance opt_to_tac : has_coe (option α) (tactic α) :=
⟨returnopt⟩

/- Decorate t's exceptions with msg -/
meta def decorate_ex (msg : format) (t : tactic α) : tactic α :=
λ s, tactic_result.cases_on (t s)
  success
  (λ opt_thunk,
     match opt_thunk with
     | some e := exception (some (λ u, msg ++ format.nest 2 (format.line ++ e u)))
     | none   := exception none
     end)

@[inline] meta def write (s' : tactic_state) : tactic unit :=
λ s, success () s'

@[inline] meta def read : tactic tactic_state :=
λ s, success s s

meta def get_options : tactic options :=
do s ← read, return s^.get_options

meta def set_options (o : options) : tactic unit :=
do s ← read, write (s^.set_options o)

meta def save_options {α : Type} (t : tactic α) : tactic α :=
do o ← get_options,
   a ← t,
   set_options o,
   return a

meta def returnex {α : Type} (e : exceptional α) : tactic α :=
λ s, match e with
| exceptional.success a      := success a s
| exceptional.exception .α f :=
  match get_options s with
  | success opt _   := exception (some (λ u, f opt)) none s
  | exception _ _ _ := exception (some (λ u, f options.mk)) none s
  end
end

meta instance ex_to_tac {α : Type} : has_coe (exceptional α) (tactic α) :=
⟨returnex⟩

end tactic

meta def tactic_format_expr (e : expr) : tactic format :=
do s ← tactic.read, return (tactic_state.format_expr s e)

meta class has_to_tactic_format (α : Type u) :=
(to_tactic_format : α → tactic format)

meta instance : has_to_tactic_format expr :=
⟨tactic_format_expr⟩

meta def tactic.pp {α : Type u} [has_to_tactic_format α] : α → tactic format :=
has_to_tactic_format.to_tactic_format

open tactic format

meta def list_to_tactic_format_aux {α : Type u} [has_to_tactic_format α] : bool → list α → tactic format
| b  []     := return $ to_fmt ""
| b (x::xs) := do
  f₁ ← pp x,
  f₂ ← list_to_tactic_format_aux ff xs,
  return $ (if ¬ b then to_fmt "," ++ line else nil) ++ f₁ ++ f₂

meta def list_to_tactic_format {α : Type u} [has_to_tactic_format α] : list α → tactic format
| []      := return $ to_fmt "[]"
| (x::xs) := do
  f ← list_to_tactic_format_aux tt (x::xs),
  return $ to_fmt "[" ++ group (nest 1 f) ++ to_fmt "]"

meta instance {α : Type u} [has_to_tactic_format α] : has_to_tactic_format (list α) :=
⟨list_to_tactic_format⟩

meta def pair_to_tactic_format_aux {α : Type u} {β : Type v} [has_to_tactic_format α] [has_to_tactic_format β] :
         α × β → tactic format
| (a, b) := do
  fa ← pp a, fb ← pp b,
  return $ to_fmt "(" ++ fa ++ ", " ++ fb ++ ")"

meta instance (α : Type u) (β : Type v) [has_to_tactic_format α] [has_to_tactic_format β] :
 has_to_tactic_format (α × β) := ⟨pair_to_tactic_format_aux⟩

meta def option_to_tactic_format {α : Type u} [has_to_tactic_format α] : option α → tactic format
| (some a) := do fa ← pp a, return (to_fmt "(some " ++ fa ++ ")")
| none     := return "none"

meta instance {α : Type u} [has_to_tactic_format α] : has_to_tactic_format (option α) :=
⟨option_to_tactic_format⟩

meta instance has_to_format_to_has_to_tactic_format (α : Type) [has_to_format α] : has_to_tactic_format α :=
⟨(λ x, return x) ∘ to_fmt⟩

namespace tactic
open tactic_state

meta def get_env : tactic environment :=
do s ← read,
   return $ env s

meta def get_decl (n : name) : tactic declaration :=
do s ← read,
   (env s)^.get n

meta def trace {α : Type u} [has_to_tactic_format α] (a : α) : tactic unit :=
do fmt ← pp a,
   return $ _root_.trace_fmt fmt (λ u, ())

meta def trace_call_stack : tactic unit :=
take state, _root_.trace_call_stack (success () state)

meta def trace_state : tactic unit :=
do s ← read,
   trace $ to_fmt s

inductive transparency
| all | semireducible | reducible | none

export transparency (reducible semireducible)

/- (eval_expr α α_as_expr e) evaluates 'e' IF 'e' has type 'α'.
   'α' must be a closed term.
   'α_as_expr' is synthesized by the code generator.
   'e' must be a closed expression at runtime. -/
meta constant eval_expr (α : Type u) {α_expr : pexpr} : expr → tactic α

/- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
meta constant result        : tactic expr
/- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   do { r ← result, s ← read, return (format_expr s r) } because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
meta constant format_result : tactic format
/- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
meta constant target        : tactic expr
meta constant intro_core    : name → tactic expr
meta constant intron        : nat → tactic unit
meta constant rename        : name → name → tactic unit
/- Clear the given local constant. The tactic fails if the given expression is not a local constant. -/
meta constant clear         : expr → tactic unit
meta constant revert_lst    : list expr → tactic nat
meta constant whnf_core     : transparency → expr → tactic expr
/- (head) eta expand the given expression -/
meta constant eta_expand    : expr → tactic expr
/- (head) beta reduction -/
meta constant beta          : expr → tactic expr
/- (head) zeta reduction -/
meta constant zeta          : expr → tactic expr
/- (head) eta reduction -/
meta constant eta           : expr → tactic expr
meta constant unify_core    : transparency → expr → expr → tactic unit
/- is_def_eq_core is similar to unify_core, but it treats metavariables as constants. -/
meta constant is_def_eq_core : transparency → expr → expr → tactic unit
/- Infer the type of the given expression.
   Remark: transparency does not affect type inference -/
meta constant infer_type    : expr → tactic expr

meta constant get_local     : name → tactic expr
/- Resolve a name using the current local context, environment, aliases, etc. -/
meta constant resolve_name  : name → tactic expr
/- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
meta constant local_context : tactic (list expr)
meta constant get_unused_name : name → option nat → tactic name
/-  Helper tactic for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (α : Type.{l_1}) (β : α -> Type.{l_2}), (Pi x : α, β x) -> (Pi x : α, β x) -> , Prop
        nat     : Type
        real    : Type
        vec.{l} : Pi (α : Type l) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        mk_app_core semireducible "rel" [f, g]
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g -/
meta constant mk_app_core   : transparency → name → list expr → tactic expr
/- Similar to mk_app, but allows to specify which arguments are explicit/implicit.
   Example, given
     a b : nat
   then
     mk_mapp_core semireducible "ite" [some (a > b), none, none, some a, some b]
   returns the application
     @ite.{1} (a > b) (nat.decidable_gt a b) nat a b -/
meta constant mk_mapp_core  : transparency → name → list (option expr) → tactic expr
/-- (mk_congr_arg h₁ h₂) is a more efficient version of (mk_app `congr_arg [h₁, h₂]) -/
meta constant mk_congr_arg  : expr → expr → tactic expr
/-- (mk_congr_fun h₁ h₂) is a more efficient version of (mk_app `congr_fun [h₁, h₂]) -/
meta constant mk_congr_fun  : expr → expr → tactic expr
/-- (mk_congr h₁ h₂) is a more efficient version of (mk_app `congr [h₁, h₂]) -/
meta constant mk_congr      : expr → expr → tactic expr
/-- (mk_eq_refl h) is a more efficient version of (mk_app `eq.refl [h]) -/
meta constant mk_eq_refl    : expr → tactic expr
/-- (mk_eq_symm h) is a more efficient version of (mk_app `eq.symm [h]) -/
meta constant mk_eq_symm    : expr → tactic expr
/-- (mk_eq_trans h₁ h₂) is a more efficient version of (mk_app `eq.trans [h₁, h₂]) -/
meta constant mk_eq_trans   : expr → expr → tactic expr
/-- (mk_eq_mp h₁ h₂) is a more efficient version of (mk_app `eq.mp [h₁, h₂]) -/
meta constant mk_eq_mp      : expr → expr → tactic expr
/-- (mk_eq_mpr h₁ h₂) is a more efficient version of (mk_app `eq.mpr [h₁, h₂]) -/
meta constant mk_eq_mpr      : expr → expr → tactic expr
/- Given a local constant t, if t has type (lhs = rhs) apply susbstitution.
   Otherwise, try to find a local constant that has type of the form (t = t') or (t' = t).
   The tactic fails if the given expression is not a local constant. -/
meta constant subst         : expr → tactic unit
meta constant exact_core    : transparency → expr → tactic unit
/-- Elaborate the given quoted expression with respect to the current main goal.
    If `allow_mvars` is tt, then metavariables are tolerated and become new goals.
    If `report_errors` is ff, then errors are reported using position information from q. -/
meta constant to_expr (q : pexpr) (allow_mvars := tt) (report_errors := ff) : tactic expr
/- Return true if the given expression is a type class. -/
meta constant is_class      : expr → tactic bool
/- Try to create an instance of the given type class. -/
meta constant mk_instance   : expr → tactic expr
/- Change the target of the main goal.
   The input expression must be definitionally equal to the current target. -/
meta constant change        : expr → tactic unit
/- (assert_core H T), adds a new goal for T, and change target to (T -> target). -/
meta constant assert_core   : name → expr → tactic unit
/- (assertv_core H T P), change target to (T -> target) if P has type T. -/
meta constant assertv_core  : name → expr → expr → tactic unit
/- (define_core H T), adds a new goal for T, and change target to  (let H : T := ?M in target) in the current goal. -/
meta constant define_core   : name → expr → tactic unit
/- (definev_core H T P), change target to (Let H : T := P in target) if P has type T. -/
meta constant definev_core  : name → expr → expr → tactic unit
/- rotate goals to the left -/
meta constant rotate_left   : nat → tactic unit
meta constant get_goals     : tactic (list expr)
meta constant set_goals     : list expr → tactic unit
/- (apply_core t approx all insts e), apply the expression e to the main goal,
   the unification is performed using the given transparency mode.
   If approx is tt, then fallback to first-order unification, and approximate context during unification.
   If all is tt, then all unassigned meta-variables are added as new goals.
   If insts is tt, then use type class resolution to instantiate unassigned meta-variables.
   It returns a list of all introduced meta variables, even the assigned ones. -/
meta constant apply_core    : transparency → bool → bool → bool → expr → tactic (list expr)
/- Create a fresh meta universe variable. -/
meta constant mk_meta_univ  : tactic level
/- Create a fresh meta-variable with the given type.
   The scope of the new meta-variable is the local context of the main goal. -/
meta constant mk_meta_var   : expr → tactic expr
/- Return the value assigned to the given universe meta-variable.
   Fail if argument is not an universe meta-variable or if it is not assigned. -/
meta constant get_univ_assignment : level → tactic level
/- Return the value assigned to the given meta-variable.
   Fail if argument is not a meta-variable or if it is not assigned. -/
meta constant get_assignment : expr → tactic expr
meta constant mk_fresh_name : tactic name
/- Return a hash code for expr that ignores inst_implicit arguments,
   and proofs. -/
meta constant abstract_hash : expr → tactic nat
/- Return the "weight" of the given expr while ignoring inst_implicit arguments,
   and proofs. -/
meta constant abstract_weight : expr → tactic nat
meta constant abstract_eq     : expr → expr → tactic bool
/- (induction_core m H rec ns) induction on H using recursor rec, names for the new hypotheses
   are retrieved from ns. If ns does not have sufficient names, then use the internal binder names
   in the recursor.
   It returns for each new goal a list of new hypotheses and a list of substitutions for hypotheses
   depending on H. The substitutions map internal names to their replacement terms. If the
   replacement is again a hypothesis the user name stays the same. The internal names are only valid
   in the original goal, not in the type context of the new goal. -/
meta constant induction_core : transparency → expr → name → list name → tactic (list (list expr × list (name × expr)))
/- (cases_core m H ns) apply cases_on recursor, names for the new hypotheses are retrieved from ns.
   H must be a local constant.
   It returns for each new goal the name of the constructor, a list of new hypotheses, and a list of
   substitutions for hypotheses depending on H. The number of new goals may be smaller than the
   number of constructors. Some goals may be discarded when the indices to not match.
   See `induction_core` for information on the list of substitutions. -/
meta constant cases_core     : transparency → expr → list name → tactic (list (name × list expr × list (name × expr)))
/- (destruct_core m e) similar to cases tactic, but does not revert/intro/clear hypotheses. -/
meta constant destruct_core    : transparency → expr → tactic unit
/- (generalize_core m e n) -/
meta constant generalize_core : transparency → expr → name → tactic unit
/- instantiate assigned metavariables in the given expression -/
meta constant instantiate_mvars : expr → tactic expr
/- Add the given declaration to the environment -/
meta constant add_decl : declaration → tactic unit
/- (doc_string env d k) return the doc string for d (if available) -/
meta constant doc_string : name → tactic string
meta constant add_doc_string : name → string → tactic unit
/--
Create an auxiliary definition with name `c` where `type` and `value` may contain local constants and
meta-variables. This function collects all dependencies (universe parameters, universe metavariables,
local constants (aka hypotheses) and metavariables).
It updates the environment in the tactic_state, and returns an expression of the form

          (c.{l_1 ... l_n} a_1 ... a_m)

where l_i's and a_j's are the collected dependencies.
-/
meta constant add_aux_decl (c : name) (type : expr) (val : expr) (is_lemma : bool) : tactic expr
meta constant module_doc_strings : tactic (list (option name × string))
/- (set_basic_attribute_core attr_name c_name persistent prio) set attribute attr_name for constant c_name with the given priority.
   If the priority is none, then use default -/
meta constant set_basic_attribute_core : name → name → bool → option nat → tactic unit
/- (unset_attribute attr_name c_name) -/
meta constant unset_attribute : name → name → tactic unit
/- (has_attribute attr_name c_name) succeeds if the declaration `decl_name`
   has the attribute `attr_name`. The result is the priority. -/
meta constant has_attribute : name → name → tactic nat

meta def set_basic_attribute : name → name → bool → tactic unit :=
λ a n p, set_basic_attribute_core a n p none

/- (copy_attribute attr_name c_name d_name) copy attribute `attr_name` from
   `src` to `tgt` if it is defined for `src` -/
meta def copy_attribute (attr_name : name) (src : name) (p : bool) (tgt : name) : tactic unit :=
try $ do
  prio ← has_attribute attr_name src,
  set_basic_attribute_core attr_name tgt p (some prio)

/-- Name of the declaration currently being elaborated. -/
meta constant decl_name : tactic name

/- (save_type_info e ref) save (typeof e) at position associated with ref -/
meta constant save_type_info : expr → expr → tactic unit
meta constant save_info_thunk : nat → nat → (unit → format) → tactic unit
meta constant report_error : nat → nat → format → tactic unit
/- Return list of currently opened namespace -/
meta constant open_namespaces : tactic (list name)
open list nat

/- Remark: set_goals will erase any solved goal -/
meta def cleanup : tactic unit :=
get_goals >>= set_goals

/- Auxiliary definition used to implement begin ... end blocks -/
meta def step {α : Type u} (t : tactic α) : tactic unit :=
t >>[tactic] cleanup

meta def istep {α : Type u} (line : nat) (col : nat) (t : tactic α) : tactic unit :=
λ s, @scope_trace _ line col ((t >>[tactic] cleanup) s)

meta def report_exception {α : Type} (line col : nat) : option (unit → format) → tactic α
| (some msg_thunk) := λ s,
  let msg := msg_thunk () ++ format.line ++ to_fmt "state:" ++ format.line ++ s^.to_format in
  (tactic.report_error line col msg >> silent_fail) s
| none := silent_fail

/- Auxiliary definition used to implement begin ... end blocks.
   It is similar to step, but it reports an error at the given line/col if the tactic t fails. -/
meta def rstep {α : Type u} (line : nat) (col : nat) (t : tactic α) : tactic unit :=
λ s, tactic_result.cases_on (istep line col t s)
  (λ a new_s, tactic_result.success () new_s)
  (λ msg_thunk e, report_exception line col msg_thunk)

meta def is_prop (e : expr) : tactic bool :=
do t ← infer_type e,
   return (to_bool (t = expr.prop))

/-- Return true iff n is the name of declaration that is a proposition. -/
meta def is_prop_decl (n : name) : tactic bool :=
do env ← get_env,
   d   ← env^.get n,
   t   ← return $ d^.type,
   is_prop t

meta def is_proof (e : expr) : tactic bool :=
infer_type e >>= is_prop

meta def whnf : expr → tactic expr :=
whnf_core semireducible

meta def whnf_no_delta : expr → tactic expr :=
whnf_core transparency.none

meta def whnf_target : tactic unit :=
target >>= whnf >>= change

meta def intro (n : name) : tactic expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then intro_core n
   else whnf_target >> intro_core n

meta def intro1 : tactic expr :=
intro `_

meta def intros : tactic (list expr) :=
do t ← target,
match t with
| expr.pi   _ _ _ _ := do H ← intro1, Hs ← intros, return (H :: Hs)
| expr.elet _ _ _ _ := do H ← intro1, Hs ← intros, return (H :: Hs)
| _                 := return []
end

meta def intro_lst : list name → tactic (list expr)
| []      := return []
| (n::ns) := do H ← intro n, Hs ← intro_lst ns, return (H :: Hs)

meta def mk_app : name → list expr → tactic expr :=
mk_app_core semireducible

meta def mk_mapp : name → list (option expr) → tactic expr :=
mk_mapp_core semireducible

meta def to_expr_strict (q : pexpr) (report_errors := ff) : tactic expr :=
to_expr q report_errors

meta def revert (l : expr) : tactic nat :=
revert_lst [l]

meta def clear_lst : list name → tactic unit
| []      := skip
| (n::ns) := do H ← get_local n, clear H, clear_lst ns

meta def unify : expr → expr → tactic unit :=
unify_core semireducible

meta def is_def_eq : expr → expr → tactic unit :=
is_def_eq_core semireducible

meta def match_not (e : expr) : tactic expr :=
match (expr.is_not e) with
| (some a) := return a
| none     := fail "expression is not a negation"
end

meta def match_eq (e : expr) : tactic (expr × expr) :=
match (expr.is_eq e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not an equality"
end

meta def match_ne (e : expr) : tactic (expr × expr) :=
match (expr.is_ne e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not a disequality"
end

meta def match_heq (e : expr) : tactic (expr × expr × expr × expr) :=
do match (expr.is_heq e) with
| (some (α, lhs, β, rhs)) := return (α, lhs, β, rhs)
| none                    := fail "expression is not a heterogeneous equality"
end

meta def match_refl_app (e : expr) : tactic (name × expr × expr) :=
do env ← get_env,
match (environment.is_refl_app env e) with
| (some (R, lhs, rhs)) := return (R, lhs, rhs)
| none                 := fail "expression is not an application of a reflexive relation"
end

meta def match_app_of (e : expr) (n : name) : tactic (list expr) :=
guard (expr.is_app_of e n) >> return e^.get_app_args

meta def get_local_type (n : name) : tactic expr :=
get_local n >>= infer_type

meta def trace_result : tactic unit :=
format_result >>= trace

meta def exact : expr → tactic unit :=
exact_core semireducible

meta def rexact : expr → tactic unit :=
exact_core reducible

/- (find_same_type t es) tries to find in es an expression with type definitionally equal to t -/
meta def find_same_type : expr → list expr → tactic expr
| e []         := failed
| e (H :: Hs) :=
  do t ← infer_type H,
     (unify e t >> return H) <|> find_same_type e Hs

meta def find_assumption (e : expr) : tactic expr :=
do ctx ← local_context, find_same_type e ctx

meta def assumption : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_same_type t ctx,
     exact H }
<|> fail "assumption tactic failed"

meta def save_info (line : nat) (col : nat) : tactic unit :=
do s ← read,
   tactic.save_info_thunk line col (λ _, tactic_state.to_format s)

notation `‹` p `›` := show p, by assumption

/- Swap first two goals, do nothing if tactic state does not have at least two goals. -/
meta def swap : tactic unit :=
do gs ← get_goals,
   match gs with
   | (g₁ :: g₂ :: rs) := set_goals (g₂ :: g₁ :: rs)
   | e                := skip
   end

/- (assert h t), adds a new goal for t, and the hypothesis (h : t) in the current goal. -/
meta def assert (h : name) (t : expr) : tactic unit :=
assert_core h t >> swap >> intro h >> swap

/- (assertv h t v), adds the hypothesis (h : t) in the current goal if v has type t. -/
meta def assertv (h : name) (t : expr) (v : expr) : tactic unit :=
assertv_core h t v >> intro h >> return ()

/- (define h t), adds a new goal for t, and the hypothesis (h : t := ?M) in the current goal. -/
meta def define  (h : name) (t : expr) : tactic unit :=
define_core h t >> swap >> intro h >> swap

/- (definev h t v), adds the hypothesis (h : t := v) in the current goal if v has type t. -/
meta def definev (h : name) (t : expr) (v : expr) : tactic unit :=
definev_core h t v >> intro h >> return ()

/- Add (h : t := pr) to the current goal -/
meta def pose (h : name) (pr : expr) : tactic unit :=
do t ← infer_type pr,
   definev h t pr

/- Add (h : t) to the current goal, given a proof (pr : t) -/
meta def note (n : name) (pr : expr) : tactic unit :=
do t ← infer_type pr,
   assertv n t pr

/- Return the number of goals that need to be solved -/
meta def num_goals     : tactic nat :=
do gs ← get_goals,
   return (length gs)

/- We have to provide the instance argument `[has_mod nat]` because
   mod for nat was not defined yet -/
meta def rotate_right (n : nat) [has_mod nat] : tactic unit :=
do ng ← num_goals,
   if ng = 0 then skip
   else rotate_left (ng - n % ng)

meta def rotate : nat → tactic unit :=
rotate_left

/- first [t_1, ..., t_n] applies the first tactic that doesn't fail.
   The tactic fails if all t_i's fail. -/
meta def first {α : Type u} : list (tactic α) → tactic α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

/- Applies the given tactic to the main goal and fails if it is not solved. -/
meta def solve1 (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []      := fail "focus tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals rs
        | gs := fail "focus tactic failed, focused goal has not been solved"
        end
   end

/- solve [t_1, ... t_n] applies the first tactic that solves the main goal. -/
meta def solve (ts : list (tactic unit)) : tactic unit :=
first $ map solve1 ts

 private meta def focus_aux : list (tactic unit) → list expr → list expr → tactic unit
| []       gs      rs := set_goals $ rs ++ gs
| (t::ts)  (g::gs) rs := do
  set_goals [g], t, rs' ← get_goals,
  focus_aux ts gs (rs ++ rs')
| (t::ts)  []      rs := fail "focus tactic failed, insufficient number of goals"

/- focus [t_1, ..., t_n] applies t_i to the i-th goal. Fails if there are less tha n goals. -/
meta def focus (ts : list (tactic unit)) : tactic unit :=
do gs ← get_goals, focus_aux ts gs []

private meta def all_goals_core (tac : tactic unit) : list expr → list expr → tactic unit
| []        ac := set_goals ac
| (g :: gs) ac :=
  do set_goals [g],
     tac,
     new_gs ← get_goals,
     all_goals_core gs (ac ++ new_gs)

/- Apply the given tactic to all goals. -/
meta def all_goals (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   all_goals_core tac gs []

private meta def any_goals_core (tac : tactic unit) : list expr → list expr → bool → tactic unit
| []        ac progress := guard progress >> set_goals ac
| (g :: gs) ac progress :=
  do set_goals [g],
     succeeded ← try_core tac,
     new_gs    ← get_goals,
     any_goals_core gs (ac ++ new_gs) (succeeded^.is_some || progress)

/- Apply the given tactic to any goal where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def any_goals (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   any_goals_core tac gs [] ff

/- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta def seq (tac1 : tactic unit) (tac2 : tactic unit) : tactic unit :=
do g::gs ← get_goals,
   set_goals [g],
   tac1, all_goals tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

meta instance : has_andthen (tactic unit) :=
⟨seq⟩

/- Applies tac if c holds -/
meta def when (c : Prop) [decidable c] (tac : tactic unit) : tactic unit :=
if c then tac else skip

meta constant is_trace_enabled_for : name → bool

/- Execute tac only if option trace.n is set to true. -/
meta def when_tracing (n : name) (tac : tactic unit) : tactic unit :=
when (is_trace_enabled_for n = tt) tac

/- Fail if there are no remaining goals. -/
meta def fail_if_no_goals : tactic unit :=
do n ← num_goals,
   when (n = 0) (fail "tactic failed, there are no goals to be solved")

/- Fail if there are unsolved goals. -/
meta def now : tactic unit :=
do n ← num_goals,
   when (n ≠ 0) (fail "now tactic failed, there are unsolved goals")

meta def apply (e : expr) : tactic unit :=
do apply_core semireducible tt ff tt e, return ()

meta def fapply (e : expr) : tactic unit :=
do apply_core semireducible tt tt tt e, return ()

/- Try to solve the main goal using type class resolution. -/
meta def apply_instance : tactic unit :=
do tgt ← target >>= instantiate_mvars,
   b   ← is_class tgt,
   if b then mk_instance tgt >>= exact
   else fail "apply_instance tactic fail, target is not a type class"

/- Create a list of universe meta-variables of the given size. -/
meta def mk_num_meta_univs : nat → tactic (list level)
| 0        := return []
| (succ n) := do
  l  ← mk_meta_univ,
  ls ← mk_num_meta_univs n,
  return (l::ls)

/- Return (expr.const c [l_1, ..., l_n]) where l_i's are fresh universe meta-variables. -/
meta def mk_const (c : name) : tactic expr :=
do env  ← get_env,
   decl ← env^.get c,
   num  ← return decl^.univ_params^.length,
   ls   ← mk_num_meta_univs num,
   return (expr.const c ls)

meta def save_const_type_info (n : name) (ref : expr) : tactic unit :=
try (do c ← mk_const n, save_type_info c ref)

/- Create a fresh universe ?u, a metavariable (?T : Type.{?u}),
   and return metavariable (?M : ?T).
   This action can be used to create a meta-variable when
   we don't know its type at creation time -/
meta def mk_mvar : tactic expr :=
do u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   mk_meta_var t

/-- Makes a sorry macro with a meta-variable as its type. -/
meta def mk_sorry : tactic expr := do
u ← mk_meta_univ,
t ← mk_meta_var (expr.sort u),
return $ expr.mk_sorry t

/-- Closes the main goal using sorry. -/
meta def admit : tactic unit :=
target >>= exact ∘ expr.mk_sorry

meta def mk_local' (pp_name : name) (bi : binder_info) (type : expr) : tactic expr := do
uniq_name ← mk_fresh_name,
return $ expr.local_const uniq_name pp_name bi type

meta def mk_local_def (pp_name : name) (type : expr) : tactic expr :=
mk_local' pp_name binder_info.default type

private meta def get_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     l     ← return (expr.local_const m n bi d),
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_pi_arity_aux new_b,
     return (r + 1)
| e                  := return 0

/- Compute the arity of the given (Pi-)type -/
meta def get_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_pi_arity_aux

/- Compute the arity of the given function -/
meta def get_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_pi_arity

meta def triv : tactic unit := mk_const `trivial >>= exact

notation `dec_trivial` := of_as_true (by tactic.triv)

meta def by_contradiction (H : name) : tactic expr :=
do tgt : expr ← target,
   (match_not tgt >> return ())
   <|>
   (mk_mapp `decidable.by_contradiction [some tgt, none] >>= apply)
   <|>
   fail "tactic by_contradiction failed, target is not a negation nor a decidable proposition (remark: when 'local attribute classical.prop_decidable [instance]' is used all propositions are decidable)",
   intro H

meta def cases (H : expr) : tactic (list (name × list expr × list (name × expr))) :=
cases_core semireducible H []

meta def cases_using : expr → list name → tactic (list (name × list expr × list (name × expr))) :=
cases_core semireducible

meta def induction : expr → name → list name → tactic (list (list expr × list (name × expr))) :=
induction_core semireducible

meta def destruct (e : expr) : tactic unit :=
destruct_core semireducible e

meta def generalize : expr → name → tactic unit :=
generalize_core semireducible

meta def generalizes : list expr → tactic unit
| []      := skip
| (e::es) := generalize e `x >> generalizes es

meta def refine (e : pexpr) (report_errors := ff) : tactic unit :=
do tgt : expr ← target,
   to_expr `(%%e : %%tgt) tt report_errors >>= exact

private meta def get_undeclared_const (env : environment) (base : name) : ℕ → name | i :=
let n := base <.> ("_aux_" ++ to_string i) in
if ¬env^.contains n then n
else get_undeclared_const (i+1)

meta def new_aux_decl_name : tactic name := do
env ← get_env, n ← decl_name,
return $ get_undeclared_const env n 1

private meta def mk_aux_decl_name : option name → tactic name
| none          := new_aux_decl_name
| (some suffix) := do p ← decl_name, return $ p ++ suffix

meta def abstract (tac : tactic unit) (suffix : option name := none) : tactic unit :=
do fail_if_no_goals,
   gs ← get_goals,
   type ← target,
   is_lemma ← is_prop type,
   m ← mk_meta_var type,
   set_goals [m],
   tac,
   n ← num_goals,
   when (n ≠ 0) (fail "abstract tactic failed, there are unsolved goals"),
   set_goals gs,
   val ← instantiate_mvars m,
   c   ← mk_aux_decl_name suffix,
   e   ← add_aux_decl c type val is_lemma,
   exact e

/- (solve_aux type tac) synthesize an element of 'type' using tactic 'tac' -/
meta def solve_aux {α : Type} (type : expr) (tac : tactic α) : tactic (α × expr) :=
do m ← mk_meta_var type,
   gs ← get_goals,
   set_goals [m],
   a ← tac,
   set_goals gs,
   return (a, m)

/-- Return tt iff 'd' is a declaration in one of the current open namespaces -/
meta def in_open_namespaces (d : name) : tactic bool :=
do ns  ← open_namespaces,
   env ← get_env,
   return $ ns^.any (λ n, n^.is_prefix_of d) && env^.contains d

end tactic

open tactic

meta def nat.to_expr : nat → tactic expr
| n :=
  if n = 0 then to_expr `(0)
  else if n = 1 then to_expr `(1)
  else do
    r : expr ← nat.to_expr (n / 2),
    if n % 2 = 0 then to_expr `(bit0 %%r)
    else to_expr `(bit1 %%r)

meta def char.to_expr : char → tactic expr
| ⟨n, pr⟩ := do e ← n^.to_expr, to_expr `(char.of_nat %%e)

meta def string.to_expr : string → tactic expr
| []      := to_expr `(string.empty)
| (c::cs) := do e ← c^.to_expr, es ← string.to_expr cs, to_expr `(string.str %%e %%es)

meta def unsigned.to_expr : unsigned → tactic expr
| ⟨n, pr⟩ := do e ← n^.to_expr, to_expr `(unsigned.of_nat %%e)

meta def name.to_expr : name → tactic expr
| name.anonymous        := to_expr `(name.anonymous)
| (name.mk_string s n)  := do es ← s^.to_expr, en ← name.to_expr n, to_expr `(name.mk_string %%es %%en)
| (name.mk_numeral i n) := do is ← i^.to_expr, en ← name.to_expr n, to_expr `(name.mk_string %%is %%en)

meta def list_name.to_expr : list name → tactic expr
| []     := to_expr `([] : list name)
| (h::t) := do eh ← h^.to_expr, et ← list_name.to_expr t, to_expr `(%%eh :: %%et)

notation [parsing_only] `command`:max := tactic unit

open tactic

namespace list

meta def for_each {α} : list α → (α → tactic unit) → tactic unit
| []      fn := skip
| (e::es) fn := do fn e, for_each es fn

meta def any_of {α β} : list α → (α → tactic β) → tactic β
| []      fn := failed
| (e::es) fn := do opt_b ← try_core (fn e),
                   match opt_b with
                   | some b := return b
                   | none   := any_of es fn
                   end
end list

/-
  Define id_locked using meta-programming because we don't have
  syntax for setting reducibility_hints.

  See module init.meta.declaration.

  Remark: id_locked is used in the builtin implementation of tactic.change
-/
run_command do
 l  ← return $ level.param `l,
 Ty ← return $ expr.sort l,
 type ← to_expr `(Π (α : %%Ty), α → α),
 val  ← to_expr `(λ (α : %%Ty) (a : α), a),
 add_decl (declaration.defn `id_locked [`l] type val reducibility_hints.opaque tt)

lemma id_locked_eq {α : Type u} (a : α) : id_locked α a = a :=
rfl
