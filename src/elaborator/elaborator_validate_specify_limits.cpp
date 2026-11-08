#include <cstdint>
#include <format>
#include <initializer_list>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_specify_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

static ScopeMap BuildSpecifyConstantScope(const ModuleDecl* mod,
                                          const ModuleItem* block) {
  ScopeMap scope;
  for (const auto& param : mod->params) scope.emplace(param.first, 0);
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kParamDecl && !item->name.empty()) {
      scope.emplace(item->name, 0);
    }
  }
  for (std::string_view sp : CollectSpecparamsInScope(mod, block)) {
    scope.emplace(sp, 0);
  }
  return scope;
}

static bool IsConstantFlag(const Expr* flag, const ScopeMap& scope) {
  if (flag->kind != ExprKind::kMinTypMax) return IsConstantExpr(flag, scope);
  for (const Expr* member : {flag->lhs, flag->condition, flag->rhs}) {
    if (!IsConstantExpr(member, scope)) return false;
  }
  return true;
}

struct FlaggedTimingCheck {
  const SpecifyItem* si;
  std::string_view task;
  Subclause subclause;
};

static void CheckTimingCheckFlag(const Expr* flag, std::string_view name,
                                 const FlaggedTimingCheck& check,
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (flag == nullptr || IsConstantFlag(flag, scope)) return;
  diag.Error(
      check.si->loc,
      std::format("{} {} is not a constant expression", check.task, name),
      check.subclause);
}

void ValidateTimingCheckFlags(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    ScopeMap scope = BuildSpecifyConstantScope(mod, item);
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      const auto& tc = si->timing_check;
      FlaggedTimingCheck check{si, "$timeskew", Subclause("31.4.2")};
      if (tc.check_kind == TimingCheckKind::kFullskew) {
        check = {si, "$fullskew", Subclause("31.4.3")};
      } else if (tc.check_kind != TimingCheckKind::kTimeskew) {
        continue;
      }
      CheckTimingCheckFlag(tc.event_based_flag, "event_based_flag", check,
                           scope, diag);
      CheckTimingCheckFlag(tc.remain_active_flag, "remain_active_flag", check,
                           scope, diag);
    }
  }
}

void ValidateTimingCheckLimitOperands(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    SignalSet specparams = CollectSpecparamsInScope(mod, item);
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      for (auto* lim : si->timing_check.limits) {
        CheckDelayExpr(lim, si->loc, specparams, diag,
                       {"timing check limit operand", Subclause("31.2")});
      }
    }
  }
}

std::optional<int64_t> FoldSpecifyLimitBinary(TokenKind op, int64_t l,
                                              int64_t r) {
  switch (op) {
    case TokenKind::kPlus:
      return l + r;
    case TokenKind::kMinus:
      return l - r;
    case TokenKind::kStar:
      return l * r;
    default:
      return std::nullopt;
  }
}

std::optional<int64_t> FoldSpecifyLimit(
    const Expr* e,
    const std::unordered_map<std::string_view, const Expr*>& specparam_values,
    int depth) {
  if (!e || depth > 32) return std::nullopt;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
      return static_cast<int64_t>(e->int_val);
    case ExprKind::kIdentifier: {
      auto it = specparam_values.find(e->text);
      if (it == specparam_values.end()) return std::nullopt;
      return FoldSpecifyLimit(it->second, specparam_values, depth + 1);
    }
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary: {
      auto v = FoldSpecifyLimit(e->lhs, specparam_values, depth + 1);
      if (!v) return std::nullopt;
      if (e->op == TokenKind::kMinus) return -*v;
      if (e->op == TokenKind::kPlus) return v;
      return std::nullopt;
    }
    case ExprKind::kBinary: {
      auto l = FoldSpecifyLimit(e->lhs, specparam_values, depth + 1);
      auto r = FoldSpecifyLimit(e->rhs, specparam_values, depth + 1);
      if (!l || !r) return std::nullopt;
      return FoldSpecifyLimitBinary(e->op, *l, *r);
    }
    default:
      return std::nullopt;
  }
}

static std::unordered_map<std::string_view, const Expr*> CollectSpecparamValues(
    const ModuleItem* item) {
  std::unordered_map<std::string_view, const Expr*> values;
  for (auto* si : item->specify_items) {
    if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
      values.emplace(si->param_name, si->param_value);
    }
  }
  return values;
}

void ReportNegativeTimingCheckLimits(
    const SpecifyItem* si,
    const std::unordered_map<std::string_view, const Expr*>& specparam_values,
    std::string_view task, DiagEngine& diag, Subclause subclause) {
  for (auto* lim : si->timing_check.limits) {
    auto v = FoldSpecifyLimit(lim, specparam_values, 0);
    if (v && *v < 0) {
      diag.Error(si->loc,
                 std::format("{} timing check limit must be a non-negative "
                             "constant expression",
                             task),
                 subclause);
    }
  }
}

void ValidateTimingCheckLimitNonNegative(const ModuleDecl* mod,
                                         DiagEngine& diag, TimingCheckKind kind,
                                         std::string_view task,
                                         Subclause subclause) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    auto specparam_values = CollectSpecparamValues(item);
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != kind) continue;
      ReportNegativeTimingCheckLimits(si, specparam_values, task, diag,
                                      subclause);
    }
  }
}

bool IsAllowedConditionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kTildeCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kAmpAmp:
    case TokenKind::kPipePipe:
    case TokenKind::kBang:
      return true;
    default:
      return false;
  }
}

static std::string ConditionOpMessage(const Expr* e) {
  std::string_view form = e->kind == ExprKind::kPostfixUnary ? "postfix"
                          : e->kind == ExprKind::kUnary      ? "unary"
                                                             : "binary";
  return std::format(
      "{} operator {} is not permitted in a state-dependent path "
      "conditional expression",
      form, TokenKindName(e->op));
}

static std::string DottedName(const Expr* e) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) return std::string(e->text);
  if (e->kind != ExprKind::kMemberAccess) return {};
  return DottedName(e->lhs) + "." + DottedName(e->rhs);
}

static void CheckConditionMemberOperand(const Expr* e, SourceLoc loc,
                                        const PortMap& port_map,
                                        DiagEngine& diag) {
  if (e->is_scope_resolution) return;
  const Expr* head = e;
  while (head->kind == ExprKind::kMemberAccess && head->lhs != nullptr) {
    head = head->lhs;
  }
  if (head->kind == ExprKind::kIdentifier &&
      port_map.find(head->text) != port_map.end()) {
    return;
  }
  diag.Error(loc,
             std::format("state-dependent path condition operand '{}' may "
                         "not be a hierarchical name reaching another scope",
                         DottedName(e)),
             Subclause("30.4.4.1"));
}

static std::string_view ForbiddenConditionForm(ExprKind kind) {
  switch (kind) {
    case ExprKind::kInside:
      return "an inside expression";
    case ExprKind::kCast:
      return "a cast";
    case ExprKind::kStreamingConcat:
      return "a streaming concatenation";
    case ExprKind::kAssignmentPattern:
      return "an assignment pattern";
    case ExprKind::kTagged:
      return "a tagged expression";
    default:
      return {};
  }
}

void CheckConditionExpr(const Expr* e, SourceLoc loc, const PortMap& port_map,
                        DiagEngine& diag) {
  if (!e) return;
  if (std::string_view form = ForbiddenConditionForm(e->kind); !form.empty()) {
    diag.Error(loc,
               std::format("{} is not permitted in a state-dependent path "
                           "conditional expression",
                           form),
               Subclause("30.4.4.1"));
    return;
  }
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      auto it = port_map.find(e->text);
      if (it != port_map.end() && it->second->direction == Direction::kOutput) {
        diag.Error(loc,
                   std::format("state-dependent path condition operand "
                               "'{}' may not be an output port",
                               e->text),
                   Subclause("30.4.4.1"));
      }
      return;
    }
    case ExprKind::kMemberAccess:
      CheckConditionMemberOperand(e, loc, port_map, diag);
      return;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      if (!IsAllowedConditionOp(e->op)) {
        diag.Error(loc, ConditionOpMessage(e), Subclause("30.4.4.1"));
      }
      CheckConditionExpr(e->lhs, loc, port_map, diag);
      return;
    case ExprKind::kBinary:
      if (!IsAllowedConditionOp(e->op)) {
        diag.Error(loc, ConditionOpMessage(e), Subclause("30.4.4.1"));
      }
      CheckConditionExpr(e->lhs, loc, port_map, diag);
      CheckConditionExpr(e->rhs, loc, port_map, diag);
      return;
    case ExprKind::kTernary:
      CheckConditionExpr(e->condition, loc, port_map, diag);
      CheckConditionExpr(e->true_expr, loc, port_map, diag);
      CheckConditionExpr(e->false_expr, loc, port_map, diag);
      return;
    case ExprKind::kSelect:
      CheckConditionExpr(e->base, loc, port_map, diag);
      CheckConditionExpr(e->index, loc, port_map, diag);
      CheckConditionExpr(e->index_end, loc, port_map, diag);
      return;
    case ExprKind::kConcatenation:
      for (auto* el : e->elements) CheckConditionExpr(el, loc, port_map, diag);
      return;
    case ExprKind::kReplicate:
      CheckConditionExpr(e->repeat_count, loc, port_map, diag);
      for (auto* el : e->elements) CheckConditionExpr(el, loc, port_map, diag);
      return;
    default:
      return;
  }
}

void CheckItemConditionExpr(const SpecifyItem* si, const PortMap& port_map,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  if (si->path.condition == nullptr) return;
  CheckConditionExpr(si->path.condition, si->loc, port_map, diag);
}

void ValidateConditionExprs(const ModuleDecl* mod, const PortMap& port_map,
                            DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckItemConditionExpr(si, port_map, diag);
    }
  }
}

void CheckPulseControlTerminals(const SpecifyItem* si, const PortMap& port_map,
                                DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kSpecparam || !si->is_pathpulse) return;
  if (si->pathpulse_input.empty() && si->pathpulse_output.empty()) return;
  auto in_it = port_map.find(si->pathpulse_input);
  if (in_it != port_map.end() &&
      in_it->second->direction == Direction::kOutput) {
    diag.Error(si->loc,
               std::format("PATHPULSE$ input terminal '{}' must be an input or "
                           "inout port",
                           si->pathpulse_input),
               Subclause("30.4.1"));
  }
  auto out_it = port_map.find(si->pathpulse_output);
  if (out_it != port_map.end() &&
      out_it->second->direction == Direction::kInput) {
    diag.Error(si->loc,
               std::format("PATHPULSE$ output terminal '{}' must be an output "
                           "or inout port",
                           si->pathpulse_output),
               Subclause("30.4.1"));
  }
}

void ValidatePulseControlTerminals(const ModuleDecl* mod,
                                   const PortMap& port_map, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckPulseControlTerminals(si, port_map, diag);
    }
  }
}

}  // namespace delta
