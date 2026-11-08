#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {
using ClockvarPredicate = std::function<bool(const Expr*)>;
using OutputClockvarNamePredicate = std::function<bool(std::string_view)>;
}  // namespace

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

void CheckClockingOutputBinding(const ClockingSignalDecl& sig,
                                DiagEngine& diag) {
  if (sig.hier_expr != nullptr &&
      (sig.direction == Direction::kOutput ||
       sig.direction == Direction::kInout) &&
      !IsLegalClockingOutputExpr(sig.hier_expr)) {
    diag.Error(
        sig.hier_expr->range.start,
        std::format("clocking {} signal '{}' is bound to an expression that "
                    "is not a legal output-port connection",
                    sig.direction == Direction::kInout ? "inout" : "output",
                    sig.name),
        Subclause("14.5"));
  }
}

}  // namespace

static std::string ClockingSignalSkewRole(const ClockingSignalDecl& sig,
                                          bool from_out_field) {
  std::string_view half =
      (from_out_field || sig.direction == Direction::kOutput) ? "output"
                                                              : "input";
  return std::format("{} skew of clocking signal '{}'", half, sig.name);
}

static std::string ClockingSkewMessage(std::string_view role,
                                       std::string_view breach,
                                       std::string_view value) {
  return std::format(
      "{} is {} ({}); a clocking skew has to be a whole number of zero or more",
      role, breach, value);
}

static void CheckClockingSkewRealValue(const Expr* delay,
                                       const ScopeMap& skew_scope,
                                       std::string_view role,
                                       DiagEngine& diag) {
  std::optional<double> rv = ConstEvalReal(delay, skew_scope);
  if (!rv.has_value()) return;
  if (*rv < 0.0) {
    diag.Error(delay->range.start,
               ClockingSkewMessage(role, "negative", std::format("{}", *rv)),
               Subclause("14.3"));
    return;
  }
  if (*rv != std::floor(*rv)) {
    diag.Error(
        delay->range.start,
        ClockingSkewMessage(role, "not an integer", std::format("{}", *rv)),
        Subclause("14.3"));
  }
}

static void CheckClockingSkew(const Expr* delay, const ScopeMap& skew_scope,
                              std::string_view role, DiagEngine& diag) {
  if (delay == nullptr) return;
  if (delay->kind == ExprKind::kTimeLiteral) return;
  if (!IsConstantExpr(delay, skew_scope)) {
    diag.Error(delay->range.start,
               "this clocking skew is not a constant expression; only "
               "constants and parameters may set a skew",
               Subclause("14.4"));
    return;
  }
  std::optional<int64_t> iv = ConstEvalInt(delay, skew_scope);
  if (iv.has_value()) {
    if (*iv < 0) {
      diag.Error(delay->range.start,
                 ClockingSkewMessage(role, "negative", std::format("{}", *iv)),
                 Subclause("14.3"));
    }
    return;
  }
  CheckClockingSkewRealValue(delay, skew_scope, role, diag);
}

static void CollectAssociatedSignals(const Expr* e,
                                     std::vector<std::string_view>& out) {
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
  } else if (e->kind == ExprKind::kSelect) {
    CollectAssociatedSignals(e->base, out);
  }
  for (const Expr* elem : e->elements) CollectAssociatedSignals(elem, out);
}

static std::vector<std::string_view> AssociatedSignals(
    const ClockingSignalDecl& sig) {
  std::vector<std::string_view> out;
  if (sig.hier_expr == nullptr) {
    out.push_back(sig.name);
  } else {
    CollectAssociatedSignals(sig.hier_expr, out);
  }
  return out;
}

void Elaborator::ValidateClockingBlock(ModuleItem* item,
                                       const RtlirModule* mod) {
  if (item->kind == ModuleItemKind::kClockingBlock && item->name.empty() &&
      !item->is_default_clocking && !item->is_global_clocking) {
    diag_.Error(item->loc, "non-default clocking block must have a name",
                Subclause("14.3"));
  }

  ScopeMap skew_scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CheckClockingSkew(item->default_input_skew_delay, skew_scope,
                    "default input skew", diag_);
  CheckClockingSkew(item->default_output_skew_delay, skew_scope,
                    "default output skew", diag_);
  for (const auto& sig : item->clocking_signals) {
    CheckClockingSkew(sig.skew_delay, skew_scope,
                      ClockingSignalSkewRole(sig, false), diag_);
    CheckClockingSkew(sig.out_skew_delay, skew_scope,
                      ClockingSignalSkewRole(sig, true), diag_);
    CheckClockingOutputBinding(sig, diag_);
  }

  if (!item->name.empty()) {
    auto& sigs = clocking_signals_[item->name];
    for (const auto& sig : item->clocking_signals) {
      sigs[sig.name] = {sig.direction, AssociatedSignals(sig)};
    }
  }
}

void Elaborator::ValidateNoFormalShadowedByBodyLocal(ModuleItem* item) {
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
                      "in the body",
                  Subclause("16.10"));
    }
  }
}

void Elaborator::ValidateRecursiveProperty(const ModuleItem* item) {
  if (item == nullptr || item->kind != ModuleItemKind::kPropertyDecl) return;

  const bool kRecursive = property_registry_.IsRecursiveProperty(item);

  if (kRecursive && item->prop_disable_iff_count > 0) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" may not use disable iff (Restriction 2)",
                Subclause("16.12.17"));
  }

  for (auto ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(ref);
    if (callee != nullptr &&
        property_registry_.ReachesRecursiveProperty(callee)) {
      diag_.Error(item->loc,
                  "negation or strong operator applied to property \"" +
                      std::string(ref) +
                      "\", which reaches a recursive property "
                      "(Restriction 1)",
                  Subclause("16.12.17"));
    }
  }

  if (property_registry_.IsOnZeroWeightCycle(item)) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" lies on a recursion cycle with no positive advance in "
                    "time (Restriction 3)",
                Subclause("16.12.17"));
  }

  ValidateRecursivePropertyArguments(item);
}

namespace {

bool RecursiveInstanceArgViolates(
    const PropertyInstanceArgInfo& inst, const ModuleItem* q, std::size_t i,
    const std::unordered_set<std::string_view>& p_formals) {
  const auto& idents = inst.arg_idents[i];

  const bool kIsSingleFormal =
      i < inst.arg_is_single_ident.size() && inst.arg_is_single_ident[i] &&
      idents.size() == 1 && p_formals.count(idents[0]) != 0;
  if (kIsSingleFormal) return false;

  bool any_p_formal = false;
  for (auto id : idents) {
    if (p_formals.count(id) != 0) {
      any_p_formal = true;
      break;
    }
  }
  if (!any_p_formal) return false;

  const bool kBoundToLocalFormal =
      i < q->prop_formal_is_local.size() && q->prop_formal_is_local[i];
  return !kBoundToLocalFormal;
}

}  // namespace

void Elaborator::ValidateRecursivePropertyArguments(const ModuleItem* item) {
  if (item->prop_instance_args.empty()) return;

  std::unordered_set<std::string_view> p_formals(item->prop_formals.begin(),
                                                 item->prop_formals.end());

  for (const auto& inst : item->prop_instance_args) {
    const ModuleItem* q = property_registry_.Find(inst.callee);
    if (q == nullptr || q->kind != ModuleItemKind::kPropertyDecl) continue;
    if (!property_registry_.ReachesRecursiveProperty(q)) continue;

    for (std::size_t i = 0; i < inst.arg_idents.size(); ++i) {
      if (!RecursiveInstanceArgViolates(inst, q, i, p_formals)) continue;
      diag_.Error(item->loc,
                  "recursive instance of \"" + std::string(inst.callee) +
                      "\" passes an actual argument that contains a formal of "
                      "\"" +
                      std::string(item->name) +
                      "\" yet is neither a formal itself nor bound to a local "
                      "variable formal (Restriction 4)",
                  Subclause("16.12.17"));
    }
  }
}

static bool HasCycleDelay(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kCycleDelay) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = HasCycleDelay(sub);
  });
  return found;
}

static bool DeclaresDefaultClocking(const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      return true;
    }
  }
  return false;
}

static void CollectSubroutineRoots(const ModuleItem* item,
                                   std::vector<ProceduralRoot>& out) {
  for (const auto* stmt : item->func_body_stmts) {
    if (stmt) out.push_back({item, stmt});
  }
}

static void CollectGenerateBodyRoots(const std::vector<ModuleItem*>& body,
                                     std::vector<ProceduralRoot>& out,
                                     bool skip_defaulted) {
  if (skip_defaulted && DeclaresDefaultClocking(body)) return;
  CollectProceduralRoots(body, out, skip_defaulted);
}

static void CollectGenerateRoots(const ModuleItem* item,
                                 std::vector<ProceduralRoot>& out,
                                 bool skip_defaulted) {
  CollectGenerateBodyRoots(item->gen_body, out, skip_defaulted);
  if (item->gen_else) {
    CollectGenerateBodyRoots(item->gen_else->gen_body, out, skip_defaulted);
  }
  for (const auto& ci : item->gen_case_items) {
    CollectGenerateBodyRoots(ci.body, out, skip_defaulted);
  }
}

void CollectProceduralRoots(const std::vector<ModuleItem*>& items,
                            std::vector<ProceduralRoot>& out,
                            bool skip_defaulted) {
  for (const auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kAlwaysBlock:
      case ModuleItemKind::kAlwaysCombBlock:
      case ModuleItemKind::kAlwaysFFBlock:
      case ModuleItemKind::kAlwaysLatchBlock:
      case ModuleItemKind::kInitialBlock:
      case ModuleItemKind::kFinalBlock:
        if (item->body) out.push_back({item, item->body});
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        CollectSubroutineRoots(item, out);
        break;
      case ModuleItemKind::kGenerateIf:
      case ModuleItemKind::kGenerateCase:
      case ModuleItemKind::kGenerateFor:
        CollectGenerateRoots(item, out, skip_defaulted);
        break;
      default:
        break;
    }
  }
}

static std::vector<const ModuleDecl*> DeclAndEnclosing(
    const CompilationUnit* unit, const ModuleDecl* decl) {
  std::vector<const ModuleDecl*> scopes = EnclosingDecls(unit, decl);
  scopes.insert(scopes.begin(), decl);
  return scopes;
}

static void ReportCycleDelayRoots(const std::vector<ProceduralRoot>& roots,
                                  DiagEngine& diag) {
  const ModuleItem* reported = nullptr;
  for (const auto& root : roots) {
    if (root.item == reported || !HasCycleDelay(root.body)) continue;
    reported = root.item;
    diag.Error(root.item->loc,
               "cycle delay (##) requires a default clocking block",
               Subclause("14.11"));
  }
}

void Elaborator::ValidateCycleDelayDefaultClocking(const ModuleDecl* decl) {
  for (const ModuleDecl* scope : DeclAndEnclosing(unit_, decl)) {
    if (DeclaresDefaultClocking(scope->items)) return;
  }
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots, true);
  ReportCycleDelayRoots(roots, diag_);
}

static void CollectClassMethodRoots(const ClassDecl* cls,
                                    std::vector<ProceduralRoot>& out) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr)
      CollectSubroutineRoots(m->method, out);
    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class != nullptr)
      CollectClassMethodRoots(m->nested_class, out);
  }
}

void ValidatePackageCycleDelays(const CompilationUnit* unit, DiagEngine& diag) {
  for (const auto* pkg : unit->packages) {
    std::vector<ProceduralRoot> roots;
    CollectProceduralRoots(pkg->items, roots);
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl)
        CollectClassMethodRoots(item->class_decl, roots);
    }
    ReportCycleDelayRoots(roots, diag);
  }
}

static const Stmt* FindIntraAssignCycleDelay(
    const Stmt* s, const ClockvarPredicate& targets_writable) {
  if (!s) return nullptr;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->cycle_delay != nullptr && s->lhs != nullptr &&
      !targets_writable(s->lhs)) {
    return s;
  }
  const Stmt* hit = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (hit) return;
    hit = FindIntraAssignCycleDelay(sub, targets_writable);
  });
  return hit;
}

void Elaborator::ValidateIntraAssignCycleDelay(const ModuleDecl* decl) {
  const ClockvarPredicate kTargetsWritable = [this](const Expr* e) {
    return ExprTargetsWritableClockvar(e);
  };
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  const ModuleItem* reported = nullptr;
  for (const auto& root : roots) {
    if (root.item == reported) continue;
    const Stmt* hit = FindIntraAssignCycleDelay(root.body, kTargetsWritable);
    if (hit == nullptr) continue;
    reported = root.item;
    diag_.Error(hit->range.start,
                "cycle delay (##) is not a legal intra-assignment delay "
                "in a blocking or nonblocking assignment",
                Subclause("14.11"));
  }
}

void Elaborator::ValidateDuplicateDefaultClocking(const ModuleDecl* decl) {
  const ModuleItem* first_default = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      if (first_default) {
        diag_.Error(item->loc,
                    "only one default clocking block is allowed per scope",
                    Subclause("14.12"));
        return;
      }
      first_default = item;
    }
  }
}

namespace {

bool DefaultClockingNamesBlock(const ModuleDecl* scope,
                               const ModuleItem* target) {
  for (const auto* other : scope->items) {
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
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (!item->is_default_clocking) continue;
    if (!item->clocking_event.empty()) continue;
    if (item->name.empty()) continue;
    const std::vector<const ModuleDecl*> kScopes =
        DeclAndEnclosing(unit_, decl);
    if (std::ranges::none_of(kScopes, [item](const ModuleDecl* scope) {
          return DefaultClockingNamesBlock(scope, item);
        })) {
      diag_.Error(item->loc,
                  "default clocking \"" + std::string(item->name) +
                      "\" does not name a clocking block",
                  Subclause("14.12"));
    }
  }
}

static void ReportContAssignsToClockvars(
    const ModuleDecl* decl, const ClockvarPredicate& targets_writable,
    DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign || !item->assign_lhs ||
        !targets_writable(item->assign_lhs)) {
      continue;
    }
    diag.Error(item->loc,
               "continuous assignment to a clockvar; a clockvar is written "
               "only by a synchronous drive",
               Subclause("14.16"));
  }
}

void Elaborator::ValidateContAssignToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  ReportContAssignsToClockvars(
      decl, [this](const Expr* e) { return ExprTargetsWritableClockvar(e); },
      diag_);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    const Expr* root = item->assign_lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect)
      root = root->base;
    if (root == nullptr || root->kind != ExprKind::kIdentifier) continue;
    if (IsOutputClockvarSignal(root->text)) {
      diag_.Error(item->loc,
                  std::format("continuous assignment to clocking output "
                              "variable '{}'",
                              root->text),
                  Subclause("14.16.2"));
    }
  }
}

bool Elaborator::IsOutputClockvarSignal(std::string_view name) const {
  for (const auto& [block_name, sigs] : clocking_signals_) {
    for (const auto& [clockvar, info] : sigs) {
      if ((info.direction == Direction::kOutput ||
           info.direction == Direction::kInout) &&
          std::ranges::find(info.associated, name) != info.associated.end()) {
        return true;
      }
    }
  }
  return false;
}

namespace {

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
                           root->text),
               Subclause("14.16.2"));
  }
}

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

namespace {

void CheckSyncDriveAssign(const Stmt* s,
                          const ClockvarPredicate& targets_writable,
                          DiagEngine& diag) {
  if (s->kind == StmtKind::kBlockingAssign && targets_writable(s->lhs)) {
    diag.Error(s->lhs->range.start,
               "a clockvar is written only by a synchronous drive (<=), not "
               "by a blocking assignment",
               Subclause("14.16"));
  }
  if (targets_writable(s->lhs)) {
    if (s->delay != nullptr) {
      diag.Error(s->delay->range.start,
                 "intra-assignment delay (#) is not a legal synchronous "
                 "drive to a clocking output variable",
                 Subclause("14.16"));
    }
  }
  if (s->lhs != nullptr && s->lhs->kind == ExprKind::kConcatenation) {
    for (const auto* elem : s->lhs->elements) {
      if (targets_writable(elem)) {
        diag.Error(s->lhs->range.start,
                   "a concatenation is not a legal synchronous drive target "
                   "for a clocking output variable",
                   Subclause("14.16"));
        break;
      }
    }
  }
}

void CheckSyncDriveProcContAssign(
    const Stmt* s, const ClockvarPredicate& targets_writable,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  if (targets_writable(s->lhs)) {
    diag.Error(s->lhs->range.start,
               "procedural continuous assignment (assign/force) to a "
               "clocking output variable is not allowed",
               Subclause("14.16"));
  } else if (s->lhs != nullptr) {
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
                      root->text),
          Subclause("14.16.2"));
    }
  }
}

}  // namespace

namespace {

void WalkStmtsForSyncDriveForm(
    const Stmt* s, const ClockvarPredicate& targets_writable,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckSyncDriveAssign(s, targets_writable, diag);
  } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    CheckSyncDriveProcContAssign(s, targets_writable, is_output_clockvar, diag);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForSyncDriveForm(sub, targets_writable, is_output_clockvar, diag);
  });
}

}  // namespace

void Elaborator::ValidateSyncDriveForm(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  const ClockvarPredicate kTargetsWritable = [this](const Expr* e) {
    return ExprTargetsWritableClockvar(e);
  };
  const OutputClockvarNamePredicate kIsOutputClockvar =
      [this](std::string_view name) { return IsOutputClockvarSignal(name); };
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  for (const auto& root : roots) {
    WalkStmtsForSyncDriveForm(root.body, kTargetsWritable, kIsOutputClockvar,
                              diag_);
  }
}

}  // namespace delta
