#include "elaborator/dollar_contexts.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/checker_actual_rules.h"
#include "elaborator/declared_types.h"
#include "elaborator/dollar_scope.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool AnyScalarChildContainsDollar(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,        e->rhs,          e->condition,   e->true_expr,
      e->false_expr, e->base,         e->index,       e->index_end,
      e->with_expr,  e->stream_range, e->repeat_count};
  for (const Expr* c : kChildren) {
    if (ContainsDollar(c)) return true;
  }
  return false;
}

}  // namespace

bool IsLoneDollar(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

bool ContainsDollar(const Expr* e) {
  if (e == nullptr) return false;
  if (IsLoneDollar(e)) return true;
  if (AnyScalarChildContainsDollar(e)) return true;
  for (const Expr* a : e->args)
    if (ContainsDollar(a)) return true;
  for (const Expr* el : e->elements)
    if (ContainsDollar(el)) return true;
  return false;
}

static bool MarkReportedAt(const SourceLoc& at, DollarReport& report) {
  return report.reported.emplace(at.file_id, at.line, at.column).second;
}

static bool MarkReported(const Expr* e, DollarReport& report) {
  return MarkReportedAt(e->range.start, report);
}

static void ReportDollar(const Expr* e, DollarReport& report) {
  if (!MarkReported(e, report)) return;
  report.diag.Error(e->range.start,
                    "'$' may stand only in a queue's dimension or select, a "
                    "value range's bound, a cycle delay range's upper bound, "
                    "a sequence, property or checker argument, or a "
                    "parameter's value",
                    Subclause("6.20.7"));
}

static void ReportDollarParam(const Expr* e, std::string_view name,
                              DollarReport& report) {
  if (!MarkReported(e, report)) return;
  report.diag.Error(
      e->range.start,
      std::format("parameter '{}' holds '$', so it may stand only where '$' "
                  "itself may, and never in a queue's dimension or select",
                  name),
      Subclause("6.20.7"));
}

static bool SelectsANonQueue(const Expr* select, const DollarScan& scan) {
  const Expr* base = select->base;
  return base != nullptr && base->kind == ExprKind::kIdentifier &&
         NamesNonQueue(&scan.scope, base->text);
}

template <typename Visit>
static void ForEachValueChild(const Expr* e, Visit visit) {
  if (e->kind == ExprKind::kMemberAccess) {
    visit(e->lhs);
    return;
  }
  if (!e->has_param_spec) ForEachExprChild(e, visit);
}

static bool IsIsunboundedCall(const Expr* e) {
  return e->kind == ExprKind::kSystemCall && e->callee == "$isunbounded" &&
         e->args.size() == 1 && e->args[0] != nullptr;
}

static bool IsShortCircuit(const Expr* e) {
  return e->kind == ExprKind::kBinary &&
         (e->op == TokenKind::kAmpAmp || e->op == TokenKind::kPipePipe);
}

static std::optional<bool> FoldIsunbounded(const Expr* arg,
                                           const DollarScan& scan) {
  if (!DollarParamNamed(arg, scan).empty()) return true;
  const bool kBounded = arg->kind == ExprKind::kIdentifier &&
                        arg->scope_prefix.empty() &&
                        RoleOf(&scan.scope, arg->text) == NameRole::kOther;
  return kBounded ? std::optional<bool>(false) : std::nullopt;
}

static std::optional<bool> FoldConnective(TokenKind op, std::optional<bool> lhs,
                                          std::optional<bool> rhs) {
  const bool kDecisive = op == TokenKind::kPipePipe;
  if (lhs == kDecisive || rhs == kDecisive) return kDecisive;
  if (lhs.has_value() && rhs.has_value()) return !kDecisive;
  return std::nullopt;
}

static std::optional<bool> FoldGuard(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return std::nullopt;
  if (IsIsunboundedCall(e)) return FoldIsunbounded(e->args[0], scan);
  if (e->kind == ExprKind::kUnary && e->op == TokenKind::kBang) {
    const std::optional<bool> kInner = FoldGuard(e->lhs, scan);
    return kInner.has_value() ? std::optional<bool>(!*kInner) : std::nullopt;
  }
  if (!IsShortCircuit(e)) return std::nullopt;
  return FoldConnective(e->op, FoldGuard(e->lhs, scan),
                        FoldGuard(e->rhs, scan));
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan);

static void CheckParamValue(const Expr* e, const DollarScan& scan);

static void CheckSpecializationValues(const Expr* e, const DollarScan& scan) {
  for (const Expr* prefix = e; prefix != nullptr;
       prefix = prefix->kind == ExprKind::kMemberAccess ? prefix->lhs
                                                        : nullptr) {
    if (!prefix->has_param_spec) continue;
    for (const Expr* value : prefix->elements) CheckParamValue(value, scan);
  }
}

static void CheckConstraintItems(const std::vector<ConstraintItem*>& items,
                                 const DollarScan& scan);

static void CheckDollarTree(const PropertyExprNode* tree,
                            const DollarScan& scan);

static void CheckAdmittingLoneDollar(const Expr* e, const DollarScan& scan) {
  if (e != nullptr && (IsLoneDollar(e) || !DollarParamNamed(e, scan).empty())) {
    return;
  }
  CheckDollarOperand(e, scan);
}

struct BoundFormal {
  std::string_view taker;
  std::string_view name;
  bool admits_dollar = true;
  bool of_checker = false;
  const Expr* default_value = nullptr;
};

template <typename Formals, typename Proj>
static size_t FormalPosition(const Formals& formals, std::string_view name,
                             size_t position, Proj proj) {
  if (name.empty()) return position;
  return static_cast<size_t>(std::ranges::find(formals, name, proj) -
                             formals.begin());
}

static BoundFormal FormalOf(const DollarTaker& taker, std::string_view name,
                            size_t position) {
  if (taker.checker != nullptr) {
    const std::vector<PortDecl>& ports = taker.checker->ports;
    const size_t kAt = FormalPosition(ports, name, position, &PortDecl::name);
    if (kAt >= ports.size()) return {};
    return {taker.checker->name, ports[kAt].name,
            CheckerFormalAdmitsDollar(taker.checker, kAt), true,
            ports[kAt].default_value};
  }
  const std::vector<std::string_view>& formals = taker.decl->prop_formals;
  const size_t kAt = FormalPosition(formals, name, position, std::identity{});
  if (kAt >= formals.size()) return {};
  return {taker.decl->name, formals[kAt], FormalAdmitsDollar(taker.decl, kAt),
          false, taker.decl->prop_formal_defaults[kAt]};
}

static size_t FormalCount(const DollarTaker& taker) {
  return taker.checker != nullptr ? taker.checker->ports.size()
                                  : taker.decl->prop_formals.size();
}

static std::string_view DollarFormalUses(const BoundFormal& formal) {
  return formal.of_checker
             ? ", an instance's actual or a nested checker's default"
             : " or an instance's actual";
}

static void CheckBoundActual(const Expr* actual, const BoundFormal& formal,
                             const DollarScan& scan) {
  const std::string_view kParam =
      actual != nullptr ? DollarParamNamed(actual, scan) : std::string_view{};
  if (kParam.empty() || formal.admits_dollar) {
    CheckAdmittingLoneDollar(actual, scan);
    return;
  }
  if (!MarkReported(actual, scan.report)) return;
  scan.report.diag.Error(
      actual->range.start,
      std::format("parameter '{}' holds '$', so it may stand only where '$' "
                  "itself may, and '$' may bind the formal '{}' of '{}' only "
                  "when that formal is untyped and referenced only as a cycle "
                  "delay range's upper bound{}",
                  kParam, formal.name, formal.taker, DollarFormalUses(formal)),
      Subclause("6.20.7"));
}

using LeftDefault = std::pair<BoundFormal, std::string_view>;

static void CheckLeftDefaults(const SourceLoc& at, const DollarTaker& taker,
                              const std::unordered_set<std::string_view>& bound,
                              const DollarScan& scan) {
  std::vector<LeftDefault> left;
  for (size_t i = 0; i < FormalCount(taker); ++i) {
    const BoundFormal kFormal = FormalOf(taker, {}, i);
    if (kFormal.default_value == nullptr || bound.count(kFormal.name) != 0 ||
        kFormal.admits_dollar) {
      continue;
    }
    const std::string_view kParam =
        DefaultDollarParam(kFormal.default_value, kFormal.taker, taker, scan);
    if (!kParam.empty()) left.emplace_back(kFormal, kParam);
  }
  if (left.empty() || !MarkReportedAt(at, scan.report)) return;
  for (const auto& [formal, param] : left) {
    scan.report.diag.Error(
        at,
        std::format("parameter '{}' holds '$', so it may stand only where '$' "
                    "itself may, and this instance leaves it as the default "
                    "of the formal '{}' of '{}', which '$' may bind only when "
                    "that formal is untyped and referenced only as a cycle "
                    "delay range's upper bound{}",
                    param, formal.name, formal.taker, DollarFormalUses(formal)),
        Subclause("6.20.7"));
  }
}

static void CheckCallActuals(const Expr* call, const DollarTaker& taker,
                             const DollarScan& scan) {
  const size_t kPositional = call->args.size() - call->arg_names.size();
  std::unordered_set<std::string_view> bound;
  for (size_t k = 0; k < call->args.size(); ++k) {
    const std::string_view kName =
        k < kPositional ? std::string_view{} : call->arg_names[k - kPositional];
    const BoundFormal kFormal = FormalOf(taker, kName, k);
    CheckBoundActual(call->args[k], kFormal, scan);
    if (call->args[k] != nullptr) bound.insert(kFormal.name);
  }
  CheckLeftDefaults(call->range.start, taker, bound, scan);
}

static void CheckInstanceActuals(const ModuleItem* item,
                                 const DollarScan& scan) {
  const auto kTaker = scan.report.dollar_takers.find(item->inst_module);
  if (kTaker == scan.report.dollar_takers.end()) {
    for (const auto& [name, actual] : item->inst_ports)
      CheckDollarOperand(actual, scan);
    return;
  }
  std::unordered_set<std::string_view> bound;
  for (size_t k = 0; k < item->inst_ports.size(); ++k) {
    const auto& [name, actual] = item->inst_ports[k];
    const BoundFormal kFormal = FormalOf(kTaker->second, name, k);
    CheckBoundActual(actual, kFormal, scan);
    if (actual != nullptr) bound.insert(kFormal.name);
  }
  if (!item->inst_wildcard)
    CheckLeftDefaults(item->loc, kTaker->second, bound, scan);
}

static void ReportDollarParamsIn(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return;
  CheckSpecializationValues(e, scan);
  const std::string_view kName = DollarParamNamed(e, scan);
  if (!kName.empty()) {
    ReportDollarParam(e, kName, scan.report);
    return;
  }
  ForEachValueChild(
      e, [&scan](const Expr* child) { ReportDollarParamsIn(child, scan); });
}

static bool IsToleranceRange(const Expr* range) {
  return range->op == TokenKind::kPlusSlashMinus ||
         range->op == TokenKind::kPlusPercentMinus;
}

static void CheckSelect(const Expr* e, const DollarScan& scan) {
  if (e->base == nullptr && !IsToleranceRange(e)) {
    CheckAdmittingLoneDollar(e->index, scan);
    CheckAdmittingLoneDollar(e->index_end, scan);
    return;
  }
  CheckDollarOperand(e->base, scan);
  const bool kOperands = e->base == nullptr || SelectsANonQueue(e, scan);
  const auto kCheck = kOperands ? CheckDollarOperand : ReportDollarParamsIn;
  kCheck(e->index, scan);
  kCheck(e->index_end, scan);
}

static void CheckAttachedOperands(const Expr* e, const DollarScan& scan) {
  if (e->inline_constraint != nullptr)
    CheckConstraintItems(e->inline_constraint->constraint_items, scan);
  CheckDollarTree(e->property_actual, scan);
  if (e->dist_items == nullptr) return;
  for (const ConstraintDistItem& item : *e->dist_items)
    CheckDollarOperand(item.weight, scan);
}

static bool CheckLeafOperand(const Expr* e, const DollarScan& scan) {
  if (IsQueueDim(e)) {
    ReportDollar(e, scan.report);
    return true;
  }
  const std::string_view kName = DollarParamNamed(e, scan);
  if (!kName.empty()) ReportDollarParam(e, kName, scan.report);
  return !kName.empty() || IsIsunboundedCall(e);
}

static bool CheckEvaluatedOperands(const Expr* e, const DollarScan& scan) {
  if (e->kind == ExprKind::kTernary) {
    CheckDollarOperand(e->condition, scan);
    const std::optional<bool> kTaken = FoldGuard(e->condition, scan);
    if (kTaken != false) CheckDollarOperand(e->true_expr, scan);
    if (kTaken != true) CheckDollarOperand(e->false_expr, scan);
    return true;
  }
  if (!IsShortCircuit(e)) return false;
  CheckDollarOperand(e->lhs, scan);
  if (FoldGuard(e->lhs, scan) != (e->op == TokenKind::kPipePipe))
    CheckDollarOperand(e->rhs, scan);
  return true;
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return;
  CheckSpecializationValues(e, scan);
  CheckAttachedOperands(e, scan);
  if (CheckLeafOperand(e, scan) || CheckEvaluatedOperands(e, scan)) return;
  if (e->kind == ExprKind::kSelect) {
    CheckSelect(e, scan);
    return;
  }
  const auto kTaker = e->kind == ExprKind::kCall
                          ? scan.report.dollar_takers.find(e->callee)
                          : scan.report.dollar_takers.end();
  if (kTaker != scan.report.dollar_takers.end()) {
    CheckCallActuals(e, kTaker->second, scan);
    return;
  }
  ForEachValueChild(
      e, [&scan](const Expr* child) { CheckDollarOperand(child, scan); });
}

static void CheckDistItem(const ConstraintDistItem& item,
                          const DollarScan& scan) {
  CheckDollarOperand(item.weight, scan);
  if (item.tolerance != nullptr) {
    CheckDollarOperand(item.lo, scan);
    CheckDollarOperand(item.tolerance, scan);
  } else if (item.is_range) {
    CheckAdmittingLoneDollar(item.lo, scan);
    CheckAdmittingLoneDollar(item.hi, scan);
  } else {
    CheckDollarOperand(item.value, scan);
  }
}

static void CheckConstraintItems(const std::vector<ConstraintItem*>& items,
                                 const DollarScan& scan) {
  for (const ConstraintItem* item : items) {
    CheckDollarOperand(item->expr, scan);
    for (const ConstraintDistItem& dist : item->dist) CheckDistItem(dist, scan);
    for (const Expr* e : item->exprs) CheckDollarOperand(e, scan);
    CheckConstraintItems(item->body, scan);
    CheckConstraintItems(item->else_body, scan);
  }
}

static void CheckUnpackedDims(const std::vector<Expr*>& dims,
                              const DollarScan& scan) {
  for (const Expr* dim : dims) {
    CheckDollarOperand(IsQueueDim(dim) ? dim->rhs : dim, scan);
  }
}

static void CheckTypeArgs(const std::vector<DataType>& args,
                          const DollarScan& scan);

static void CheckDeclaredDims(const DataType& type,
                              const std::vector<Expr*>& unpacked_dims,
                              const DollarScan& scan) {
  CheckTypeArgs(type.type_params, scan);
  CheckDollarOperand(type.packed_dim_left, scan);
  CheckDollarOperand(type.packed_dim_right, scan);
  for (const auto& [left, right] : type.extra_packed_dims) {
    CheckDollarOperand(left, scan);
    CheckDollarOperand(right, scan);
  }
  CheckUnpackedDims(unpacked_dims, scan);
}

static void CheckTypeArgs(const std::vector<DataType>& args,
                          const DollarScan& scan) {
  for (const DataType& arg : args) {
    if (arg.type_name.empty() && arg.type_ref_expr != nullptr) {
      CheckParamValue(arg.type_ref_expr, scan);
    } else {
      CheckDeclaredDims(arg, {}, scan);
    }
  }
}

static void CheckEvents(const std::vector<EventExpr>& events,
                        const DollarScan& scan) {
  for (const EventExpr& event : events) {
    CheckDollarOperand(event.signal, scan);
    CheckDollarOperand(event.iff_condition, scan);
  }
}

static void CheckParamValue(const Expr* e, const DollarScan& scan) {
  if (e == nullptr || ContainsDollar(e)) return;
  CheckAdmittingLoneDollar(e, scan);
}

static void CheckBounds(const SeqCycleDelay& bounds, const DollarScan& scan) {
  CheckDollarOperand(bounds.min_expr, scan);
  if (bounds.max_expr != bounds.min_expr)
    CheckAdmittingLoneDollar(bounds.max_expr, scan);
}

static void CheckDollarSequence(const ModuleItem* seq, const DollarScan& scan) {
  CheckEvents(seq->seq_clock, scan);
  ForEachBody(seq->seq_linear, [&scan](const SeqLinearBody& body) {
    for (const SeqCycleDelay& delay : body.delays) CheckBounds(delay, scan);
    for (const SeqRepetition& rep : body.repetitions) CheckBounds(rep, scan);
    for (const SeqLocalDecl& local : body.locals)
      CheckDollarOperand(local.init, scan);
    for (const auto& clock : body.clocks) CheckEvents(clock, scan);
    CheckEvents(body.clock_out, scan);
  });
  ForEachBodyExpr(seq->seq_linear,
                  [&scan](const Expr* e) { CheckDollarOperand(e, scan); });
}

static void CheckDollarTree(const PropertyExprNode* tree,
                            const DollarScan& scan) {
  ForEachTreeNode(tree, [&scan](const PropertyExprNode& node) {
    CheckDollarOperand(node.boolean, scan);
    CheckDollarOperand(node.range_min, scan);
    CheckAdmittingLoneDollar(node.range_max, scan);
    for (const auto& values : node.case_values) {
      for (const Expr* value : values) CheckDollarOperand(value, scan);
    }
    CheckEvents(node.clock, scan);
    if (node.sequence != nullptr) CheckDollarSequence(node.sequence, scan);
  });
}

static void CheckDollarDeclaration(const ModuleItem* decl,
                                   const DollarScan& outer) {
  for (const Expr* actual : decl->prop_formal_defaults)
    CheckAdmittingLoneDollar(actual, outer);
  DollarScope scope;
  scope.outer = &outer.scope;
  scope.others.insert(decl->prop_formals.begin(), decl->prop_formals.end());
  for (const SeqLocalDecl& local : decl->prop_locals)
    scope.others.insert(local.name);
  const DollarScan kScan{scope, outer.report};
  for (const SeqLocalDecl& local : decl->prop_locals)
    CheckDollarOperand(local.init, kScan);
  CheckEvents(decl->prop_clock, kScan);
  CheckDollarOperand(decl->prop_disable_iff, kScan);
  CheckDollarOperand(decl->prop_body_expr, kScan);
  CheckDollarTree(decl->prop_body_tree, kScan);
  CheckDollarSequence(decl, kScan);
}

static void CheckDollarStmt(const Stmt* s, const DollarScan& scan);

static void CheckTakenBranches(const Stmt* s, const DollarScan& scan) {
  const std::optional<bool> kTaken = FoldGuard(s->condition, scan);
  if (kTaken.value_or(true)) CheckDollarStmt(s->then_branch, scan);
  if (!kTaken.value_or(false)) CheckDollarStmt(s->else_branch, scan);
}

static void CheckDollarStmt(const Stmt* s, const DollarScan& scan) {
  if (s == nullptr) return;
  CheckDollarOperand(s->assert_disable_iff, scan);
  CheckDollarTree(s->assert_property, scan);
  if (s->assert_sequence != nullptr)
    CheckDollarSequence(s->assert_sequence, scan);
  const std::vector<Expr*>& dims = s->var_unpacked_dims;
  ForEachChildExpr(s, [&scan, &dims](const Expr* e) {
    if (std::ranges::find(dims, e) == dims.end()) CheckDollarOperand(e, scan);
  });
  if (s->kind == StmtKind::kCheckerInstantiation && s->decl_item != nullptr)
    CheckInstanceActuals(s->decl_item, scan);
  if (s->kind == StmtKind::kIf) {
    CheckTakenBranches(s, scan);
    return;
  }
  ForEachChildStmt(s,
                   [&scan](Stmt* const& sub) { CheckDollarStmt(sub, scan); });
}

static void CheckProcedure(const Stmt* body, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteLocalNames(body, scope);
  CheckDollarStmt(body, {scope, outer.report});
}

static void NoteFormals(const std::vector<FunctionArg>& formals,
                        const DollarScan& outer, DollarScope& scope) {
  for (const FunctionArg& arg : formals) {
    CheckDollarOperand(arg.default_value, outer);
    NoteDeclaredName(arg.name, arg.data_type, arg.unpacked_dims, scope);
  }
}

static void CheckSubroutine(const ModuleItem* item, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteFormals(item->func_args, outer, scope);
  for (const Stmt* s : item->func_body_stmts) NoteLocalNames(s, scope);
  const DollarScan kInner{scope, outer.report};
  for (const Stmt* s : item->func_body_stmts) CheckDollarStmt(s, kInner);
}

static void CheckDollarItems(const std::vector<ModuleItem*>& items,
                             const DollarScan& outer,
                             const InstanceParams* instance);

static void CheckGenerateArms(const ModuleItem* item, const DollarScan& scan) {
  for (const ModuleItem* arm = item; arm != nullptr; arm = arm->gen_else) {
    CheckDollarOperand(arm->gen_cond, scan);
    const std::optional<bool> kTaken = FoldGuard(arm->gen_cond, scan);
    if (kTaken.value_or(true)) CheckDollarItems(arm->gen_body, scan, nullptr);
    if (kTaken.value_or(false)) return;
  }
}

static void CheckGenerate(const ModuleItem* item, const DollarScan& scan) {
  CheckDollarStmt(item->gen_init, scan);
  CheckDollarStmt(item->gen_step, scan);
  CheckGenerateArms(item, scan);
  for (const GenerateCaseItem& arm : item->gen_case_items) {
    for (const Expr* pattern : arm.patterns) CheckDollarOperand(pattern, scan);
    CheckDollarItems(arm.body, scan, nullptr);
  }
}

static void CheckDollarClass(const ClassDecl* cls, const DollarScan& outer);

static void CheckDollarCovergroup(const CovergroupDecl* group,
                                  const DollarScan& outer);

static void CheckDollarItem(const ModuleItem* item, const DollarScan& scan) {
  switch (item->kind) {
    case ModuleItemKind::kVarDecl:
      CheckDollarOperand(item->init_expr, scan);
      break;
    case ModuleItemKind::kNetDecl:
      CheckDollarOperand(item->init_expr, scan);
      CheckDeclaredDims(item->data_type, item->unpacked_dims, scan);
      break;
    case ModuleItemKind::kModuleInst:
      CheckInstanceActuals(item, scan);
      for (const auto& [name, value] : item->inst_params)
        CheckParamValue(value, scan);
      break;
    case ModuleItemKind::kParamDecl:
      if (scan.scope.overridden.count(item->name) == 0)
        CheckParamValue(item->init_expr, scan);
      break;
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kPropertyDecl:
      CheckDollarDeclaration(item, scan);
      break;
    default:
      for (const auto& [target, value] : item->defparam_assigns)
        CheckDollarOperand(value, scan);
      break;
  }
  CheckDollarOperand(item->assign_lhs, scan);
  CheckDollarOperand(item->assign_rhs, scan);
  CheckProcedure(item->body, scan);
  CheckSubroutine(item, scan);
  CheckGenerate(item, scan);
  CheckEvents(item->clocking_event, scan);
  for (const ModuleItem* decl : item->clocking_decls)
    CheckDollarItem(decl, scan);
  if (item->class_decl != nullptr) CheckDollarClass(item->class_decl, scan);
  if (item->covergroup != nullptr)
    CheckDollarCovergroup(item->covergroup, scan);
}

static void CheckCovergroupRanges(
    const std::vector<CovergroupValueRange>& ranges, const DollarScan& scan) {
  for (const CovergroupValueRange& range : ranges) {
    const bool kBounds = range.kind == CovergroupValueRangeKind::kRange;
    const auto kCheck = kBounds ? CheckAdmittingLoneDollar : CheckDollarOperand;
    kCheck(range.lo, scan);
    kCheck(range.hi, scan);
  }
}

static void CheckTransitions(const std::vector<TransSet>& sets,
                             const DollarScan& scan) {
  for (const TransSet& set : sets) {
    for (const TransRangeList& step : set.steps) {
      CheckCovergroupRanges(step.items, scan);
      CheckDollarOperand(step.repeat_lo, scan);
      CheckDollarOperand(step.repeat_hi, scan);
    }
  }
}

static void CheckBinsOrOptions(const BinsOrOptions& bins,
                               const DollarScan& scan) {
  CheckDollarOperand(bins.option.value, scan);
  CheckDollarOperand(bins.array_size, scan);
  CheckCovergroupRanges(bins.ranges, scan);
  CheckDollarOperand(bins.with_expr, scan);
  CheckDollarOperand(bins.set_expr, scan);
  CheckTransitions(bins.transitions, scan);
  CheckDollarOperand(bins.iff, scan);
}

static void CheckCoverPoint(const CoverPointDecl* point,
                            const DollarScan& scan) {
  if (point->has_data_type) CheckDeclaredDims(point->data_type, {}, scan);
  CheckDollarOperand(point->expr, scan);
  CheckDollarOperand(point->iff, scan);
  for (const BinsOrOptions& bins : point->bins) CheckBinsOrOptions(bins, scan);
}

static void CheckSelectExpression(const SelectExpression* select,
                                  const DollarScan& scan) {
  if (select == nullptr) return;
  CheckCovergroupRanges(select->intersect, scan);
  CheckSelectExpression(select->lhs, scan);
  CheckSelectExpression(select->rhs, scan);
  CheckDollarOperand(select->expr, scan);
  CheckAdmittingLoneDollar(select->matches, scan);
}

static void CheckCoverCross(const CoverCrossDecl* cross,
                            const DollarScan& scan) {
  CheckDollarOperand(cross->iff, scan);
  for (const CrossBodyItem& item : cross->body) {
    if (item.function != nullptr) CheckDollarItem(item.function, scan);
    CheckDollarOperand(item.option.value, scan);
    CheckSelectExpression(item.bins.select, scan);
    CheckDollarOperand(item.bins.iff, scan);
  }
}

static void CheckDollarCovergroup(const CovergroupDecl* group,
                                  const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteFormals(group->formals, outer, scope);
  NoteFormals(group->event.sample_formals, outer, scope);
  const DollarScan kScan{scope, outer.report};
  CheckEvents(group->event.clocking, kScan);
  for (const CoverageSpecOrOption& item : group->items) {
    CheckDollarOperand(item.option.value, kScan);
    if (item.cover_point != nullptr) CheckCoverPoint(item.cover_point, kScan);
    if (item.cover_cross != nullptr) CheckCoverCross(item.cover_cross, kScan);
  }
}

static void CheckClassParamValues(const ClassDecl* cls,
                                  const DollarScan& scan) {
  for (const auto& [name, value] : cls->params) {
    if (cls->type_param_names.count(name) == 0) CheckParamValue(value, scan);
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param)
      CheckParamValue(m->init_expr, scan);
  }
  CheckTypeArgs(cls->base_class_type_params, scan);
}

static void CheckDollarClass(const ClassDecl* cls, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  DollarClassStore store;
  NoteClassNames(cls, outer.report.params, store, scope);
  const DollarScan kScan{scope, outer.report};
  CheckClassParamValues(cls, kScan);
  for (const Expr* arg : cls->extends_args) CheckDollarOperand(arg, kScan);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && !m->is_param)
      CheckDollarOperand(m->init_expr, kScan);
    if (m->method != nullptr) CheckDollarItem(m->method, kScan);
    CheckConstraintItems(m->constraint_items, kScan);
    if (m->nested_class != nullptr) CheckDollarClass(m->nested_class, kScan);
    if (m->covergroup != nullptr) CheckDollarCovergroup(m->covergroup, kScan);
  }
}

static void CheckDollarItems(const std::vector<ModuleItem*>& items,
                             const DollarScan& outer,
                             const InstanceParams* instance) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteItemNames(items, outer.report.params, instance, scope);
  const DollarScan kScan{scope, outer.report};
  for (const ModuleItem* item : items) {
    CheckDollarItem(item, kScan);
    ForEachItemDeclaredType(item, [&kScan](const DeclaredType& declared) {
      CheckDeclaredDims(declared.type, declared.unpacked_dims, kScan);
    });
  }
}

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         const InstanceParams& instance, DiagEngine& diag) {
  DollarTakers takers = UnitDollarTakers(unit);
  AddDollarTakers(decl->items, nullptr, takers);
  const DollarParams kParams = UnitDollarParams(unit);
  DollarReport report{takers, kParams, diag, {}};
  DollarScope unit_scope;
  NoteUnitNames(unit, kParams, unit_scope);
  DollarScope ports;
  ports.outer = &unit_scope;
  for (const auto& [name, value] : decl->params)
    NoteInstanceParam(name, instance, ports);
  for (const PortDecl& port : decl->ports)
    NoteDeclaredName(port.name, port.data_type, port.unpacked_dims, ports);
  const DollarScan kScan{ports, report};
  for (const auto& [name, value] : decl->params) {
    if (decl->type_param_names.count(name) == 0 &&
        ports.overridden.count(name) == 0) {
      CheckParamValue(value, kScan);
    }
  }
  for (const PortDecl& port : decl->ports)
    CheckDeclaredDims(port.data_type, port.unpacked_dims, kScan);
  CheckDollarItems(decl->items, kScan, &instance);
}

void CheckUnitDollarOperands(const CompilationUnit& unit, DiagEngine& diag) {
  const DollarTakers kTakers = UnitDollarTakers(unit);
  const DollarParams kParams = UnitDollarParams(unit);
  DollarReport report{kTakers, kParams, diag, {}};
  const DollarScope kRoot;
  const DollarScan kPackageScan{kRoot, report};
  for (const PackageDecl* pkg : unit.packages)
    CheckDollarItems(pkg->items, kPackageScan, nullptr);
  DollarScope unit_scope;
  NoteUnitNames(unit, kParams, unit_scope);
  const DollarScan kScan{unit_scope, report};
  CheckDollarItems(unit.cu_items, kScan, nullptr);
  for (const ClassDecl* cls : unit.classes) {
    CheckDollarClass(cls, kScan);
    ForEachClassDeclaredType(cls, [&kScan](const DeclaredType& declared) {
      CheckDeclaredDims(declared.type, declared.unpacked_dims, kScan);
    });
  }
}

}  // namespace delta
