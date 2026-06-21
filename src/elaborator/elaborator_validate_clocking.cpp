#include <format>
#include <functional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {
// Predicate that decides whether an expression targets a writable clockvar.
using ClockvarPredicate = std::function<bool(const Expr*)>;
// Predicate that decides whether a name is an output/inout clockvar signal.
using OutputClockvarNamePredicate = std::function<bool(std::string_view)>;
}  // namespace

// §14.5: an expression bound to a clocking output (or inout) signal forwards to
// a module output port, so it must be a legal output-port connection — that is,
// an assignable target. Assignable forms are a simple name, a hierarchical
// reference, a bit/part-select of one, or a concatenation of such targets.
// Non-assignable forms (literals, operator expressions, calls, replications)
// cannot drive an output port and are therefore rejected. Inputs impose no such
// restriction, since any readable expression is a valid input-port connection.
static bool IsLegalClockingOutputExpr(const Expr* e) {
  if (e == nullptr) return false;
  switch (e->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kMemberAccess:
      return true;
    case ExprKind::kSelect:
      return IsLegalClockingOutputExpr(e->base);
    case ExprKind::kConcatenation: {
      if (e->elements.empty()) return false;
      for (const Expr* el : e->elements) {
        if (!IsLegalClockingOutputExpr(el)) return false;
      }
      return true;
    }
    default:
      return false;
  }
}

namespace {

// §14.5: a hierarchical expression bound to a clocking output or inout signal
// must be a legal output-port connection (an assignable target); inputs are
// not.
void CheckClockingOutputBinding(const ClockingSignalDecl& sig,
                                DiagEngine& diag) {
  if (sig.hier_expr != nullptr &&
      (sig.direction == Direction::kOutput ||
       sig.direction == Direction::kInout) &&
      !IsLegalClockingOutputExpr(sig.hier_expr)) {
    diag.Error(
        sig.hier_expr->range.start,
        std::format("clocking {} signal '{}' is bound to an expression that "
                    "is not a legal output-port connection (§14.5)",
                    sig.direction == Direction::kInout ? "inout" : "output",
                    sig.name));
  }
}

}  // namespace

void Elaborator::ValidateClockingBlock(ModuleItem* item,
                                       const RtlirModule* mod) {
  // §14.3: only an actual clocking_declaration is subject to the naming rule;
  // an inline clocking event in a property/sequence/assert item is not a
  // clocking block and is reached here only because it shares the item carrier.
  // §14.3/§14.13: a clocking block must be named unless it is the default
  // clocking or a global clocking, both of which may be anonymous.
  if (item->kind == ModuleItemKind::kClockingBlock && item->name.empty() &&
      !item->is_default_clocking && !item->is_global_clocking) {
    diag_.Error(item->loc, "non-default clocking block must have a name");
  }

  // §14.4: a clocking skew shall be a constant expression; a parameter is an
  // acceptable form. Any skew delay that cannot be folded against the module's
  // parameter scope (e.g. a reference to a net or variable) violates the rule.
  ScopeMap skew_scope = mod ? BuildParamScope(mod) : ScopeMap{};
  auto check_skew = [&](const Expr* delay) {
    if (delay != nullptr && !IsConstantExpr(delay, skew_scope)) {
      diag_.Error(delay->range.start,
                  "clocking skew shall be a constant expression (§14.4)");
    }
  };
  check_skew(item->default_input_skew_delay);
  check_skew(item->default_output_skew_delay);
  for (const auto& sig : item->clocking_signals) {
    check_skew(sig.skew_delay);
    check_skew(sig.out_skew_delay);
    CheckClockingOutputBinding(sig, diag_);
  }

  if (!item->name.empty()) {
    auto& sigs = clocking_signals_[item->name];
    for (const auto& sig : item->clocking_signals) {
      sigs[sig.name] = {sig.direction};
    }
  }
}

void Elaborator::ValidateNoFormalShadowedByBodyLocal(ModuleItem* item) {
  // §16.10: a formal-argument identifier cannot be redeclared in the body of
  // the same sequence/property declaration as an
  // assertion_variable_declaration. The two name lists are harvested by the
  // parser; the elaborator only has to flag any overlap.
  if (item->prop_formals.empty() || item->prop_seq_assert_vars.empty()) {
    return;
  }
  std::unordered_set<std::string_view> formal_set(item->prop_formals.begin(),
                                                  item->prop_formals.end());
  for (auto body_var : item->prop_seq_assert_vars) {
    if (formal_set.count(body_var) != 0) {
      diag_.Error(item->loc,
                  "local variable \"" + std::string(body_var) +
                      "\" is a formal argument and cannot be redeclared "
                      "in the body (§16.10)");
    }
  }
}

void Elaborator::ValidateRecursiveProperty(const ModuleItem* item) {
  if (item == nullptr || item->kind != ModuleItemKind::kPropertyDecl) return;

  const bool kRecursive = property_registry_.IsRecursiveProperty(item);

  // §16.12.17 Restriction 2 / §F.7 RESTRICTION 2: disable iff cannot be used in
  // the declaration of a recursive property. (This mirrors the rule that
  // disable iff cannot be nested.) The accept_on/reject_on family is *not*
  // affected: those operators may appear inside a recursive property.
  if (kRecursive && item->prop_disable_iff_count > 0) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" may not use disable iff (§16.12.17 Restriction 2)");
  }

  // §16.12.17 Restriction 1 / §F.7 RESTRICTION 1: the negation operator not and
  // the strong operators (s_nexttime, s_eventually, s_always, s_until,
  // s_until_with) cannot be applied to a property expression that instantiates
  // a property from which a recursive property is reachable.
  for (auto ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(ref);
    if (callee != nullptr &&
        property_registry_.ReachesRecursiveProperty(callee)) {
      diag_.Error(item->loc,
                  "negation or strong operator applied to property \"" +
                      std::string(ref) +
                      "\", which reaches a recursive property "
                      "(§16.12.17 Restriction 1)");
    }
  }

  // §16.12.17 Restriction 3 / §F.7 RESTRICTION 3: every recursive instance must
  // occur after a positive advance in time; a self-instantiation with no
  // intervening time advance would leave the recursion stuck at one cycle.
  if (item->prop_has_untimed_self_recursion) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" instantiates itself with no positive advance in time "
                    "(§16.12.17 Restriction 3)");
  }

  // §16.12.17 Restriction 4 / §F.7 RESTRICTION 4 applies to every recursive
  // instance regardless of whether the enclosing property is itself recursive.
  ValidateRecursivePropertyArguments(item);
}

namespace {

// §16.12.17 Restriction 4: whether actual argument `i` of recursive instance
// `inst` (of property `q`) violates the rule. Legal when (a) it is itself a
// single formal of p, (b) no formal of p appears, or (c) bound to a local of q.
bool RecursiveInstanceArgViolates(
    const PropertyInstanceArgInfo& inst, const ModuleItem* q, std::size_t i,
    const std::unordered_set<std::string_view>& p_formals) {
  const auto& idents = inst.arg_idents[i];

  // (a) the actual argument expression e is itself a formal of p.
  const bool kIsSingleFormal =
      i < inst.arg_is_single_ident.size() && inst.arg_is_single_ident[i] &&
      idents.size() == 1 && p_formals.count(idents[0]) != 0;
  if (kIsSingleFormal) return false;

  // (b) no formal argument of p appears in e.
  bool any_p_formal = false;
  for (auto id : idents) {
    if (p_formals.count(id) != 0) {
      any_p_formal = true;
      break;
    }
  }
  if (!any_p_formal) return false;

  // (c) e is bound to a local variable formal argument of q (positional).
  const bool kBoundToLocalFormal =
      i < q->prop_formal_is_local.size() && q->prop_formal_is_local[i];
  return !kBoundToLocalFormal;
}

}  // namespace

void Elaborator::ValidateRecursivePropertyArguments(const ModuleItem* item) {
  if (item->prop_instance_args.empty()) return;

  // Formal arguments of the enclosing property p.
  std::unordered_set<std::string_view> p_formals(item->prop_formals.begin(),
                                                 item->prop_formals.end());

  for (const auto& inst : item->prop_instance_args) {
    const ModuleItem* q = property_registry_.Find(inst.callee);
    if (q == nullptr || q->kind != ModuleItemKind::kPropertyDecl) continue;
    // Restriction 4 constrains only instances of a property that participates
    // in the recursion (a recursive instance).
    if (!property_registry_.ReachesRecursiveProperty(q)) continue;

    for (std::size_t i = 0; i < inst.arg_idents.size(); ++i) {
      if (!RecursiveInstanceArgViolates(inst, q, i, p_formals)) continue;
      diag_.Error(item->loc,
                  "recursive instance of \"" + std::string(inst.callee) +
                      "\" passes an actual argument that contains a formal of "
                      "\"" +
                      std::string(item->name) +
                      "\" yet is neither a formal itself nor bound to a local "
                      "variable formal (§16.12.17 Restriction 4)");
    }
  }
}

namespace {

// Report a clockvar direction violation for a member-access expression `e`: a
// write (lvalue) to an input clockvar or a read from an output clockvar.
// (Templated so the private nested info type need not be named here.)
template <typename ClockingSignalMap>
void CheckClockvarMemberAccessDirection(
    const Expr* e, bool is_lvalue, const ClockingSignalMap& clocking_signals,
    DiagEngine& diag) {
  if (e->kind != ExprKind::kMemberAccess || !e->lhs ||
      e->lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  auto block_it = clocking_signals.find(e->lhs->text);
  if (block_it == clocking_signals.end()) return;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
    member = e->rhs->text;
  } else if (!e->text.empty()) {
    member = e->text;
  }
  if (member.empty()) return;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return;
  if (is_lvalue && sig_it->second.direction == Direction::kInput) {
    diag.Error(e->range.start, std::format("write to input clockvar '{}.{}'",
                                           e->lhs->text, member));
  }
  if (!is_lvalue && sig_it->second.direction == Direction::kOutput) {
    diag.Error(e->range.start, std::format("read from output clockvar '{}.{}'",
                                           e->lhs->text, member));
  }
}

}  // namespace

void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  CheckClockvarMemberAccessDirection(e, is_lvalue, clocking_signals_, diag_);

  if (!is_lvalue) {
    CheckClockvarAccessExpr(e->lhs, false);
    CheckClockvarAccessExpr(e->rhs, false);
    CheckClockvarAccessExpr(e->condition, false);
    CheckClockvarAccessExpr(e->true_expr, false);
    CheckClockvarAccessExpr(e->false_expr, false);
    for (auto* arg : e->args) CheckClockvarAccessExpr(arg, false);
    for (auto* elem : e->elements) CheckClockvarAccessExpr(elem, false);
  }
}

void Elaborator::WalkStmtsForClockvarAccess(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckClockvarAccessExpr(s->lhs, true);
    CheckClockvarAccessExpr(s->rhs, false);
  } else {
    CheckClockvarAccessExpr(s->expr, false);
    CheckClockvarAccessExpr(s->rhs, false);
  }
  for (auto* sub : s->stmts) WalkStmtsForClockvarAccess(sub);
  WalkStmtsForClockvarAccess(s->then_branch);
  WalkStmtsForClockvarAccess(s->else_branch);
  WalkStmtsForClockvarAccess(s->body);
  WalkStmtsForClockvarAccess(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForClockvarAccess(ci.body);
}

void Elaborator::ValidateClockvarAccess(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForClockvarAccess(item->body);
    }
  }
}

static bool HasCycleDelay(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kCycleDelay) return true;
  for (auto* sub : s->stmts) {
    if (HasCycleDelay(sub)) return true;
  }
  if (HasCycleDelay(s->then_branch)) return true;
  if (HasCycleDelay(s->else_branch)) return true;
  if (HasCycleDelay(s->body)) return true;
  if (HasCycleDelay(s->for_body)) return true;
  for (auto& ci : s->case_items) {
    if (HasCycleDelay(ci.body)) return true;
  }
  return false;
}

void Elaborator::ValidateCycleDelayDefaultClocking(const ModuleDecl* decl) {
  bool has_default = false;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      has_default = true;
      break;
    }
  }
  if (has_default) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body && HasCycleDelay(item->body)) {
      diag_.Error(item->loc,
                  "cycle delay (##) requires a default clocking block");
    }
  }
}

// §14.11: locate an assignment that carries a cycle-delay intra-assignment
// timing control. A synchronous drive (§14.16) reaches a clocking-block
// variable through a member access (e.g. cb.sig or vif.cb.sig), so a target
// that is a simple name can only be the illegal intra-assignment form. The walk
// returns the offending statement so its source location can be reported.
static const Stmt* FindIntraAssignCycleDelay(const Stmt* s) {
  if (!s) return nullptr;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->cycle_delay != nullptr && s->lhs != nullptr &&
      s->lhs->kind == ExprKind::kIdentifier) {
    return s;
  }
  for (auto* sub : s->stmts) {
    if (const auto* hit = FindIntraAssignCycleDelay(sub)) return hit;
  }
  if (const auto* hit = FindIntraAssignCycleDelay(s->then_branch)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->else_branch)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->body)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->for_body)) return hit;
  for (auto& ci : s->case_items) {
    if (const auto* hit = FindIntraAssignCycleDelay(ci.body)) return hit;
  }
  return nullptr;
}

void Elaborator::ValidateIntraAssignCycleDelay(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      if (const Stmt* hit = FindIntraAssignCycleDelay(item->body)) {
        diag_.Error(hit->range.start,
                    "cycle delay (##) is not a legal intra-assignment delay "
                    "in a blocking or nonblocking assignment");
      }
    }
  }
}

void Elaborator::ValidateDuplicateDefaultClocking(const ModuleDecl* decl) {
  const ModuleItem* first_default = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      if (first_default) {
        diag_.Error(item->loc,
                    "only one default clocking block is allowed per scope");
        return;
      }
      first_default = item;
    }
  }
}

namespace {

// §14.12: true when some inline clocking block (carrying an @(event)) other
// than `target` shares its name, so `target` names a real clocking block.
bool DefaultClockingNamesBlock(const ModuleDecl* decl,
                               const ModuleItem* target) {
  for (const auto* other : decl->items) {
    if (other == target) continue;
    if (other->kind == ModuleItemKind::kClockingBlock &&
        !other->clocking_event.empty() && other->name == target->name) {
      return true;
    }
  }
  return false;
}

}  // namespace

void Elaborator::ValidateDefaultClockingReference(const ModuleDecl* decl) {
  // §14.12: a "default clocking <id>;" assignment statement designates an
  // existing clocking block as the default. Its clocking_identifier shall be
  // the name of a clocking block. The assignment form is distinguished from
  // the inline declaration form by carrying no clocking event (the inline
  // form always declares an @(event)).
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (!item->is_default_clocking) continue;
    if (!item->clocking_event.empty()) continue;  // inline declaration form
    if (item->name.empty()) continue;
    if (!DefaultClockingNamesBlock(decl, item)) {
      diag_.Error(item->loc, "default clocking \"" + std::string(item->name) +
                                 "\" does not name a clocking block");
    }
  }
}

void Elaborator::ValidateDuplicateGlobalClocking(const ModuleDecl* decl) {
  const ModuleItem* first_global = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      if (first_global) {
        diag_.Error(item->loc,
                    "only one global clocking block is allowed per scope");
        return;
      }
      first_global = item;
    }
  }
}

namespace {

bool ExprRefsGlobalClock(const Expr* e);

// Recurse into every scalar (single-child) sub-expression slot of `e`.
bool AnyScalarChildRefsGlobalClock(const Expr* e) {
  return ExprRefsGlobalClock(e->lhs) || ExprRefsGlobalClock(e->rhs) ||
         ExprRefsGlobalClock(e->condition) ||
         ExprRefsGlobalClock(e->true_expr) ||
         ExprRefsGlobalClock(e->false_expr) || ExprRefsGlobalClock(e->base) ||
         ExprRefsGlobalClock(e->index) || ExprRefsGlobalClock(e->index_end) ||
         ExprRefsGlobalClock(e->repeat_count) ||
         ExprRefsGlobalClock(e->with_expr);
}

bool ExprRefsGlobalClock(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$global_clock") {
    return true;
  }
  if (AnyScalarChildRefsGlobalClock(e)) return true;
  for (auto* a : e->args) {
    if (ExprRefsGlobalClock(a)) return true;
  }
  for (auto* el : e->elements) {
    if (ExprRefsGlobalClock(el)) return true;
  }
  return false;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s);

// Recurse into every nested-statement slot of `s`; returns the first
// descendant hit, or nullptr.
const Expr* FindGlobalClockRefInSubStmts(const Stmt* s) {
  for (auto* sub : s->stmts) {
    if (auto* hit = FindGlobalClockRefInStmt(sub)) return hit;
  }
  if (auto* hit = FindGlobalClockRefInStmt(s->then_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->else_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->body)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->for_body)) return hit;
  for (auto& ci : s->case_items) {
    if (auto* hit = FindGlobalClockRefInStmt(ci.body)) return hit;
  }
  return nullptr;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s) {
  if (!s) return nullptr;
  if (ExprRefsGlobalClock(s->expr)) return s->expr;
  if (ExprRefsGlobalClock(s->lhs)) return s->lhs;
  if (ExprRefsGlobalClock(s->rhs)) return s->rhs;
  if (ExprRefsGlobalClock(s->condition)) return s->condition;
  if (ExprRefsGlobalClock(s->assert_expr)) return s->assert_expr;
  if (ExprRefsGlobalClock(s->for_cond)) return s->for_cond;
  for (const auto& ev : s->events) {
    if (ExprRefsGlobalClock(ev.signal)) return ev.signal;
  }
  return FindGlobalClockRefInSubStmts(s);
}

// True when `decl` declares a global clocking block in this scope.
bool DeclHasGlobalClocking(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      return true;
    }
  }
  return false;
}

// First $global_clock reference in a module item's slots, or nullptr.
const Expr* FindGlobalClockRefInItem(const ModuleItem* item) {
  const Expr* ref = nullptr;
  if (item->body) ref = FindGlobalClockRefInStmt(item->body);
  if (!ref && ExprRefsGlobalClock(item->init_expr)) ref = item->init_expr;
  if (!ref && ExprRefsGlobalClock(item->assign_lhs)) ref = item->assign_lhs;
  if (!ref && ExprRefsGlobalClock(item->assign_rhs)) ref = item->assign_rhs;
  if (!ref && ExprRefsGlobalClock(item->prop_body_expr)) {
    ref = item->prop_body_expr;
  }
  if (!ref) {
    for (const auto& ev : item->sensitivity) {
      if (ExprRefsGlobalClock(ev.signal)) {
        ref = ev.signal;
        break;
      }
    }
  }
  return ref;
}

}  // namespace

void Elaborator::ValidateGlobalClockReference(const ModuleDecl* decl) {
  if (DeclHasGlobalClocking(decl)) return;

  for (const auto* item : decl->items) {
    const Expr* ref = FindGlobalClockRefInItem(item);
    if (ref) {
      diag_.Error(ref->range.start,
                  "$global_clock has no effective global clocking declaration "
                  "in any enclosing scope up to the top-level hierarchy block");
      return;
    }
  }
}

void Elaborator::ValidateContAssignToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    // §14.16.2: a continuous assignment to a variable that is associated with
    // an output (or inout) clockvar is illegal. The target may be the whole
    // variable or a bit-/part-select of it, so resolve through any selects to
    // the root identifier; a select target is rejected exactly as the whole
    // variable would be. This mirrors the root resolution the primitive and
    // procedural-continuous checks already perform for the same prohibition.
    const Expr* root = item->assign_lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect)
      root = root->base;
    if (root == nullptr || root->kind != ExprKind::kIdentifier) continue;
    if (IsOutputClockvarSignal(root->text)) {
      diag_.Error(item->loc,
                  std::format("continuous assignment to clocking output "
                              "variable '{}'",
                              root->text));
    }
  }
}

bool Elaborator::IsOutputClockvarSignal(std::string_view name) const {
  // §14.16.2: a clocking output/inout is implicitly tied to a same-named signal
  // in the enclosing scope (§14.3). Match the bare variable name against the
  // output/inout clockvar members collected across every clocking block.
  for (const auto& [block_name, sigs] : clocking_signals_) {
    auto it = sigs.find(name);
    if (it != sigs.end() && (it->second.direction == Direction::kOutput ||
                             it->second.direction == Direction::kInout)) {
      return true;
    }
  }
  return false;
}

namespace {

// §14.16.2: it shall be illegal to drive a variable associated with an output
// clockvar from a primitive (the gate-output terminal `t` resolved to its
// root).
void CheckPrimitiveOutputTerminal(
    const Expr* t, const OutputClockvarNamePredicate& is_output_clockvar,
    DiagEngine& diag) {
  const Expr* root = t;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root != nullptr && root->kind == ExprKind::kIdentifier &&
      is_output_clockvar(root->text)) {
    diag.Error(root->range.start,
               std::format("primitive output drives variable '{}', which is "
                           "associated with a clocking output",
                           root->text));
  }
}

// Check the output terminal(s) of one gate instance. For buf/not gates every
// terminal but the last is an output; otherwise the first terminal is the one
// output.
void CheckGateInstOutputTerminals(
    const ModuleItem* item,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  const auto& terms = item->gate_terminals;
  if (terms.empty()) return;
  if (item->gate_kind == GateKind::kBuf || item->gate_kind == GateKind::kNot) {
    for (size_t i = 0; i + 1 < terms.size(); ++i) {
      CheckPrimitiveOutputTerminal(terms[i], is_output_clockvar, diag);
    }
  } else {
    CheckPrimitiveOutputTerminal(terms[0], is_output_clockvar, diag);
  }
}

}  // namespace

void Elaborator::ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  const OutputClockvarNamePredicate kIsOutputClockvar =
      [this](std::string_view name) { return IsOutputClockvarSignal(name); };
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    CheckGateInstOutputTerminals(item, kIsOutputClockvar, diag_);
  }
}

// §14.16: a synchronous drive reaches a clocking-block output (or inout)
// through a member access such as cb.sig, optionally wrapped in a bit-select
// or slice (cb.sig[2], cb.sig[8:2]). Returns true when `e` designates such a
// writable clockvar. Input clockvars are excluded here; writes to them are
// rejected separately by the clockvar-access check.
bool Elaborator::ExprTargetsWritableClockvar(const Expr* e) const {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto block_it = clocking_signals_.find(e->lhs->text);
  if (block_it == clocking_signals_.end()) return false;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier)
    member = e->rhs->text;
  else if (!e->text.empty())
    member = e->text;
  if (member.empty()) return false;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return false;
  return sig_it->second.direction == Direction::kOutput ||
         sig_it->second.direction == Direction::kInout;
}

namespace {

// Validate the synchronous-drive form of a blocking/nonblocking assignment.
void CheckSyncDriveAssign(const Stmt* s,
                          const ClockvarPredicate& targets_writable,
                          DiagEngine& diag) {
  if (targets_writable(s->lhs)) {
    // §14.16: the only timing control permitted on a synchronous drive is a
    // leading cycle delay (## ...). A regular intra-assignment delay (# ...)
    // is not a legal form of synchronous drive to a clockvar.
    if (s->delay != nullptr) {
      diag.Error(s->delay->range.start,
                 "intra-assignment delay (#) is not a legal synchronous "
                 "drive to a clocking output variable");
    }
  }
  // §14.16: the clockvar_expression of a synchronous drive is a bit-select,
  // slice, or whole clockvar; a concatenation target is not allowed.
  if (s->lhs != nullptr && s->lhs->kind == ExprKind::kConcatenation) {
    for (const auto* elem : s->lhs->elements) {
      if (targets_writable(elem)) {
        diag.Error(s->lhs->range.start,
                   "a concatenation is not a legal synchronous drive target "
                   "for a clocking output variable");
        break;
      }
    }
  }
}

// Validate a procedural continuous assignment (assign/force) arm.
void CheckSyncDriveProcContAssign(
    const Stmt* s, const ClockvarPredicate& targets_writable,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  // §14.16: writing to a clockvar by any means other than a synchronous
  // drive is an error; procedural continuous assignment (assign/force) is
  // explicitly disallowed.
  if (targets_writable(s->lhs)) {
    diag.Error(s->lhs->range.start,
               "procedural continuous assignment (assign/force) to a "
               "clocking output variable is not allowed");
  } else if (s->lhs != nullptr) {
    // §14.16.2: it is likewise illegal to write the underlying variable that
    // an output clockvar is tied to with a procedural continuous assignment.
    const Expr* root = s->lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect)
      root = root->base;
    if (root != nullptr && root->kind == ExprKind::kIdentifier &&
        is_output_clockvar(root->text)) {
      diag.Error(
          root->range.start,
          std::format("procedural continuous assignment (assign/force) to "
                      "variable '{}', which is associated with a clocking "
                      "output, is not allowed",
                      root->text));
    }
  }
}

}  // namespace

void Elaborator::WalkStmtsForSyncDriveForm(const Stmt* s) {
  if (!s) return;
  const ClockvarPredicate kTargetsWritable = [this](const Expr* e) {
    return ExprTargetsWritableClockvar(e);
  };
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckSyncDriveAssign(s, kTargetsWritable, diag_);
  } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    const OutputClockvarNamePredicate kIsOutputClockvar =
        [this](std::string_view name) { return IsOutputClockvarSignal(name); };
    CheckSyncDriveProcContAssign(s, kTargetsWritable, kIsOutputClockvar, diag_);
  }
  for (auto* sub : s->stmts) WalkStmtsForSyncDriveForm(sub);
  WalkStmtsForSyncDriveForm(s->then_branch);
  WalkStmtsForSyncDriveForm(s->else_branch);
  WalkStmtsForSyncDriveForm(s->body);
  WalkStmtsForSyncDriveForm(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForSyncDriveForm(ci.body);
}

void Elaborator::ValidateSyncDriveForm(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) WalkStmtsForSyncDriveForm(item->body);
  }
}

}  // namespace delta
