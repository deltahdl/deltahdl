#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

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

void Elaborator::ValidateClockingBlock(ModuleItem* item,
                                       const RtlirModule* mod) {
  if (item->name.empty() && !item->is_default_clocking) {
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

    // §14.5: a hierarchical expression bound to a clocking output or inout
    // signal must be a legal output-port connection (an assignable target).
    // A clocking inout is shorthand for an input and an output sharing the
    // same signal, so it must meet the output-port rule as well — though a
    // plain variable, being assignable, remains acceptable. Input signals are
    // unconstrained here, as any readable expression is a valid input.
    if (sig.hier_expr != nullptr &&
        (sig.direction == Direction::kOutput ||
         sig.direction == Direction::kInout) &&
        !IsLegalClockingOutputExpr(sig.hier_expr)) {
      diag_.Error(
          sig.hier_expr->range.start,
          std::format("clocking {} signal '{}' is bound to an expression that "
                      "is not a legal output-port connection (§14.5)",
                      sig.direction == Direction::kInout ? "inout" : "output",
                      sig.name));
    }
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
      const auto& idents = inst.arg_idents[i];

      // (a) the actual argument expression e is itself a formal of p.
      const bool kIsSingleFormal =
          i < inst.arg_is_single_ident.size() && inst.arg_is_single_ident[i] &&
          idents.size() == 1 && p_formals.count(idents[0]) != 0;
      if (kIsSingleFormal) continue;

      // (b) no formal argument of p appears in e.
      bool any_p_formal = false;
      for (auto id : idents) {
        if (p_formals.count(id) != 0) {
          any_p_formal = true;
          break;
        }
      }
      if (!any_p_formal) continue;

      // (c) e is bound to a local variable formal argument of q (positional).
      const bool kBoundToLocalFormal =
          i < q->prop_formal_is_local.size() && q->prop_formal_is_local[i];
      if (kBoundToLocalFormal) continue;

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

void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier) {
    auto block_it = clocking_signals_.find(e->lhs->text);
    if (block_it != clocking_signals_.end()) {
      std::string_view member;
      if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
        member = e->rhs->text;
      } else if (!e->text.empty()) {
        member = e->text;
      }
      if (!member.empty()) {
        auto sig_it = block_it->second.find(member);
        if (sig_it != block_it->second.end()) {
          if (is_lvalue && sig_it->second.direction == Direction::kInput) {
            diag_.Error(e->range.start,
                        std::format("write to input clockvar '{}.{}'",
                                    e->lhs->text, member));
          }
          if (!is_lvalue && sig_it->second.direction == Direction::kOutput) {
            diag_.Error(e->range.start,
                        std::format("read from output clockvar '{}.{}'",
                                    e->lhs->text, member));
          }
        }
      }
    }
  }

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
    bool names_block = false;
    for (const auto* other : decl->items) {
      if (other == item) continue;
      if (other->kind == ModuleItemKind::kClockingBlock &&
          !other->clocking_event.empty() && other->name == item->name) {
        names_block = true;
        break;
      }
    }
    if (!names_block) {
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

bool ExprRefsGlobalClock(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$global_clock") {
    return true;
  }
  if (ExprRefsGlobalClock(e->lhs)) return true;
  if (ExprRefsGlobalClock(e->rhs)) return true;
  if (ExprRefsGlobalClock(e->condition)) return true;
  if (ExprRefsGlobalClock(e->true_expr)) return true;
  if (ExprRefsGlobalClock(e->false_expr)) return true;
  if (ExprRefsGlobalClock(e->base)) return true;
  if (ExprRefsGlobalClock(e->index)) return true;
  if (ExprRefsGlobalClock(e->index_end)) return true;
  if (ExprRefsGlobalClock(e->repeat_count)) return true;
  if (ExprRefsGlobalClock(e->with_expr)) return true;
  for (auto* a : e->args) {
    if (ExprRefsGlobalClock(a)) return true;
  }
  for (auto* el : e->elements) {
    if (ExprRefsGlobalClock(el)) return true;
  }
  return false;
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

}  // namespace

void Elaborator::ValidateGlobalClockReference(const ModuleDecl* decl) {
  bool has_global = false;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      has_global = true;
      break;
    }
  }
  if (has_global) return;

  for (const auto* item : decl->items) {
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

void Elaborator::ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    const auto& terms = item->gate_terminals;
    if (terms.empty()) continue;

    auto check = [&](const Expr* t) {
      // §14.16.2: it shall be illegal to drive a variable associated with an
      // output clockvar from a primitive.
      const Expr* root = t;
      while (root != nullptr && root->kind == ExprKind::kSelect)
        root = root->base;
      if (root != nullptr && root->kind == ExprKind::kIdentifier &&
          IsOutputClockvarSignal(root->text)) {
        diag_.Error(
            root->range.start,
            std::format("primitive output drives variable '{}', which is "
                        "associated with a clocking output",
                        root->text));
      }
    };

    // For buf/not gates every terminal but the last is an output; for the
    // other driving gates the first terminal is the single output.
    if (item->gate_kind == GateKind::kBuf ||
        item->gate_kind == GateKind::kNot) {
      for (size_t i = 0; i + 1 < terms.size(); ++i) check(terms[i]);
    } else {
      check(terms[0]);
    }
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

void Elaborator::WalkStmtsForSyncDriveForm(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (ExprTargetsWritableClockvar(s->lhs)) {
      // §14.16: the only timing control permitted on a synchronous drive is a
      // leading cycle delay (## ...). A regular intra-assignment delay (# ...)
      // is not a legal form of synchronous drive to a clockvar.
      if (s->delay != nullptr) {
        diag_.Error(s->delay->range.start,
                    "intra-assignment delay (#) is not a legal synchronous "
                    "drive to a clocking output variable");
      }
    }
    // §14.16: the clockvar_expression of a synchronous drive is a bit-select,
    // slice, or whole clockvar; a concatenation target is not allowed.
    if (s->lhs != nullptr && s->lhs->kind == ExprKind::kConcatenation) {
      for (const auto* elem : s->lhs->elements) {
        if (ExprTargetsWritableClockvar(elem)) {
          diag_.Error(s->lhs->range.start,
                      "a concatenation is not a legal synchronous drive target "
                      "for a clocking output variable");
          break;
        }
      }
    }
  } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    // §14.16: writing to a clockvar by any means other than a synchronous
    // drive is an error; procedural continuous assignment (assign/force) is
    // explicitly disallowed.
    if (ExprTargetsWritableClockvar(s->lhs)) {
      diag_.Error(s->lhs->range.start,
                  "procedural continuous assignment (assign/force) to a "
                  "clocking output variable is not allowed");
    } else if (s->lhs != nullptr) {
      // §14.16.2: it is likewise illegal to write the underlying variable that
      // an output clockvar is tied to with a procedural continuous assignment.
      const Expr* root = s->lhs;
      while (root != nullptr && root->kind == ExprKind::kSelect)
        root = root->base;
      if (root != nullptr && root->kind == ExprKind::kIdentifier &&
          IsOutputClockvarSignal(root->text)) {
        diag_.Error(
            root->range.start,
            std::format("procedural continuous assignment (assign/force) to "
                        "variable '{}', which is associated with a clocking "
                        "output, is not allowed",
                        root->text));
      }
    }
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

static void WalkStmtsForSequenceEvents(
    Stmt* s, const std::unordered_set<std::string_view>& seq_names,
    bool in_automatic, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (auto& ev : s->events) {
      if (!ev.signal) continue;
      std::string_view name;
      bool has_args = false;
      if (ev.signal->kind == ExprKind::kIdentifier) {
        name = ev.signal->text;
      } else if (ev.signal->kind == ExprKind::kCall) {
        name = ev.signal->callee;
        has_args = !ev.signal->args.empty();
      }
      if (!name.empty() && seq_names.count(name) != 0) {
        ev.is_sequence_event = true;

        if (has_args && in_automatic) {
          diag.Error(s->range.start,
                     "sequence event arguments shall not reference "
                     "automatic variables");
        }
      }
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForSequenceEvents(sub, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->then_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->else_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->body, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->for_body, seq_names, in_automatic, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForSequenceEvents(ci.body, seq_names, in_automatic, diag);
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl) {
  if (sequence_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      if (item->body) {
        WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                   sequence_names_, false, diag_);
      }
    }

    if (item->kind == ModuleItemKind::kTaskDecl && item->body) {
      WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body), sequence_names_,
                                 item->is_automatic, diag_);
    }
  }
}

static bool IsSingleSubroutineCall(const Stmt* action) {
  if (!action) return true;
  if (action->kind == StmtKind::kNull) return true;
  if (action->kind != StmtKind::kExprStmt) return false;
  if (!action->expr) return false;
  return action->expr->kind == ExprKind::kCall ||
         action->expr->kind == ExprKind::kSystemCall;
}

static bool ContainsPostponedIllegalStmt(const Stmt* s) {
  if (!s) return false;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kCycleDelay:
      return true;
    default:
      break;
  }
  for (auto* sub : s->stmts) {
    if (ContainsPostponedIllegalStmt(sub)) return true;
  }
  if (ContainsPostponedIllegalStmt(s->then_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->else_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->body)) return true;
  if (ContainsPostponedIllegalStmt(s->for_body)) return true;
  for (const auto& ci : s->case_items) {
    if (ContainsPostponedIllegalStmt(ci.body)) return true;
  }
  return false;
}

static bool CalleeBodyHasPostponedIllegal(const ModuleItem* callee) {
  if (!callee) return false;
  if (callee->body && ContainsPostponedIllegalStmt(callee->body)) return true;
  for (auto* s : callee->func_body_stmts) {
    if (ContainsPostponedIllegalStmt(s)) return true;
  }
  return false;
}

using DeferredSubroutineMap =
    std::unordered_map<std::string_view, const ModuleItem*>;

static void CheckFinalDeferredCallee(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  if (CalleeBodyHasPostponedIllegal(it->second)) {
    diag.Warning(
        action->range.start,
        std::format("§16.4: final deferred assertion calls '{}', whose body "
                    "contains statements not legally callable in the "
                    "Postponed region (§4.4.2.9)",
                    action->expr->callee));
  }
}

static void CheckDeferredCallRefArgs(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  const auto& formals = it->second->func_args;
  const auto& actuals = action->expr->args;
  size_t n = std::min(formals.size(), actuals.size());
  for (size_t i = 0; i < n; ++i) {
    if (formals[i].direction != Direction::kRef) continue;
    const Expr* a = actuals[i];
    if (!a) continue;
    if (a->kind == ExprKind::kMemberAccess) {
      diag.Error(
          a->range.start,
          std::format("§16.4: cannot pass dynamic variable as actual for "
                      "ref{} formal '{}' in deferred-assertion call",
                      formals[i].is_const ? " const" : "", formals[i].name));
    }
  }
}

static void CheckDeferredActionStmt(const Stmt* s,
                                    const DeferredSubroutineMap& subs,
                                    DiagEngine& diag) {
  if (!s->is_deferred) return;
  if (s->kind != StmtKind::kAssertImmediate &&
      s->kind != StmtKind::kAssumeImmediate &&
      s->kind != StmtKind::kCoverImmediate) {
    return;
  }
  if (s->assert_pass_stmt && !IsSingleSubroutineCall(s->assert_pass_stmt)) {
    diag.Warning(s->assert_pass_stmt->range.start,
                 "§16.4: deferred assertion pass action shall be a single "
                 "subroutine call");
  }
  if (s->assert_fail_stmt && !IsSingleSubroutineCall(s->assert_fail_stmt)) {
    diag.Warning(s->assert_fail_stmt->range.start,
                 "§16.4: deferred assertion fail action shall be a single "
                 "subroutine call");
  }

  if (s->is_final_deferred) {
    CheckFinalDeferredCallee(s->assert_pass_stmt, subs, diag);
    CheckFinalDeferredCallee(s->assert_fail_stmt, subs, diag);
  }

  CheckDeferredCallRefArgs(s->assert_pass_stmt, subs, diag);
  CheckDeferredCallRefArgs(s->assert_fail_stmt, subs, diag);
}

void Elaborator::WalkStmtsForDeferredActions(const Stmt* s) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForDeferredActions(sub);
  WalkStmtsForDeferredActions(s->then_branch);
  WalkStmtsForDeferredActions(s->else_branch);
  WalkStmtsForDeferredActions(s->body);
  WalkStmtsForDeferredActions(s->for_body);
  WalkStmtsForDeferredActions(s->assert_pass_stmt);
  WalkStmtsForDeferredActions(s->assert_fail_stmt);
  for (const auto& ci : s->case_items) WalkStmtsForDeferredActions(ci.body);
}

void Elaborator::ValidateDeferredAssertionActions(const ModuleDecl* decl) {
  deferred_subroutine_map_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      deferred_subroutine_map_[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    if (item->body) {
      WalkStmtsForDeferredActions(item->body);
    }
  }
}

}  // namespace delta
