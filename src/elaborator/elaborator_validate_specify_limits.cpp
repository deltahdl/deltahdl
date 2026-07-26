#include <algorithm>
#include <format>
#include <functional>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_specify_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ValidateTimingCheckLimitOperands(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    SignalSet specparams = CollectSpecparams(item);
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      for (auto* lim : si->timing_check.limits) {
        CheckDelayExpr(lim, si->loc, specparams, diag,
                       "timing check limit operand");
      }
    }
  }
}

// §31.4.1, Table 31-7: folds one specify-block constant limit expression to a
// signed integer so its sign can be checked. It resolves only the constant
// forms a timing-check limit may legally take -- an integer literal, a
// specparam reference (whose value expression is folded in turn), and unary or
// binary arithmetic over them (§31.2 already confines limit operands to
// literals and specparams). Anything it cannot fold -- an unknown identifier,
// an unsupported operator, x/z, a real -- yields no value, so callers flag only
// a limit that is provably negative. The depth guard stops a runaway recursion
// should a specparam reference itself.
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
      if (e->op == TokenKind::kPlus) return *v;
      return std::nullopt;
    }
    case ExprKind::kBinary: {
      auto l = FoldSpecifyLimit(e->lhs, specparam_values, depth + 1);
      auto r = FoldSpecifyLimit(e->rhs, specparam_values, depth + 1);
      if (!l || !r) return std::nullopt;
      switch (e->op) {
        case TokenKind::kPlus:
          return *l + *r;
        case TokenKind::kMinus:
          return *l - *r;
        case TokenKind::kStar:
          return *l * *r;
        default:
          return std::nullopt;
      }
    }
    default:
      return std::nullopt;
  }
}

// Pass: §31.4.1, Table 31-7 -- the limit of a $skew timing check is a
// non-negative constant expression. A limit that folds to a negative constant
// is rejected; a limit that cannot be folded to a concrete integer is left
// alone, so only a provably-negative limit is diagnosed.
void ValidateSkewLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kSkew) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$skew timing check limit must be a non-negative constant "
                     "expression");
        }
      }
    }
  }
}

// Pass: §31.4.2, Table 31-8 -- the limit of a $timeskew timing check is a
// non-negative constant expression, mirroring the $skew rule of §31.4.1. A
// limit that folds to a negative constant is rejected; a limit that cannot be
// folded to a concrete integer is left alone, so only a provably-negative limit
// is diagnosed.
void ValidateTimeskewLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kTimeskew) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$timeskew timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.4.3, Table 31-9 -- both limits of a $fullskew timing check (limit1,
// the maximum delay by which the data event may trail the reference event, and
// limit2, the maximum delay by which the reference event may trail the data
// event) are non-negative constant expressions. Both limits live in the
// timing check's limits list, so iterating the list checks each of them; only a
// limit that folds to a provably-negative constant is diagnosed, matching the
// $skew/$timeskew rules.
void ValidateFullskewLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kFullskew) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$fullskew timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.4.4, Table 31-10 -- both the limit (the pulse width below which a
// violation is reported) and the optional threshold (the glitch width below
// which no violation is reported) of a $width timing check are non-negative
// constant expressions. Both live in the timing check's limits list -- the
// limit first, the threshold second when present -- so iterating the list
// checks each of them; a limit or threshold that folds to a provably-negative
// constant is rejected while one that cannot be folded to a concrete integer is
// left alone, matching the $skew/$timeskew/$fullskew rules.
void ValidateWidthLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kWidth) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$width timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.4.5, Table 31-11 -- the limit of a $period timing check is a
// non-negative constant expression. $period takes a single limit (its data
// event is derived from the reference event, so there is no second limit like
// the $width threshold), so a limit that folds to a negative constant is
// illegal and is rejected; a limit that cannot be folded to a concrete integer
// is left alone, so only a provably-negative limit is diagnosed, matching the
// $width/$hold/$skew/$timeskew/$fullskew rules.
void ValidatePeriodLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kPeriod) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$period timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.3.2, Table 31-2 -- the limit of a $hold timing check is a
// non-negative constant expression. Standalone $hold carries a single limit
// (the negative-limit forms belong to $setuphold/$recrem, which use separate
// signed limits), so a limit that folds to a negative constant is illegal and
// is rejected; a limit that cannot be folded to a concrete integer is left
// alone, so only a provably-negative limit is diagnosed, matching the
// $skew/$timeskew/$fullskew rules.
void ValidateHoldLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kHold) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$hold timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.3.4, Table 31-4 -- the limit of a $removal timing check is a
// non-negative constant expression. $removal carries a single limit (unlike the
// signed-limit two-sided checks $setuphold/$recrem), so a limit that folds to a
// negative constant is illegal and is rejected; a limit that cannot be folded
// to a concrete integer is left alone, so only a provably-negative limit is
// diagnosed, matching the $hold/$skew/$timeskew/$fullskew rules.
void ValidateRemovalLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kRemoval) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$removal timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// Pass: §31.3.5, Table 31-5 -- the limit of a $recovery timing check is a
// non-negative constant expression. Like $hold and $removal (and unlike the
// signed-limit two-sided checks $setuphold/$recrem), $recovery carries a single
// limit, so a limit that folds to a negative constant is illegal and rejected;
// a limit that cannot be folded to a concrete integer is left alone, so only a
// provably-negative limit is diagnosed.
void ValidateRecoveryLimitNonNegative(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::unordered_map<std::string_view, const Expr*> specparam_values;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
        specparam_values.emplace(si->param_name, si->param_value);
      }
    }
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      if (si->timing_check.check_kind != TimingCheckKind::kRecovery) continue;
      for (auto* lim : si->timing_check.limits) {
        auto v = FoldSpecifyLimit(lim, specparam_values, 0);
        if (v && *v < 0) {
          diag.Error(si->loc,
                     "$recovery timing check limit must be a non-negative "
                     "constant expression");
        }
      }
    }
  }
}

// §30.4.4.1, Table 30-1: the operators permitted in a state-dependent path
// conditional expression -- bitwise, reduction, logical, and equality forms.
// Arithmetic, relational, shift, case-equality, and wildcard-equality operators
// are excluded and must be rejected.
bool IsAllowedConditionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:       // bitwise negation
    case TokenKind::kAmp:         // bitwise AND / reduction AND
    case TokenKind::kPipe:        // bitwise OR / reduction OR
    case TokenKind::kCaret:       // bitwise XOR / reduction XOR
    case TokenKind::kCaretTilde:  // bitwise / reduction XNOR
    case TokenKind::kTildeCaret:  // bitwise / reduction XNOR (alternate
                                  // spelling)
    case TokenKind::kTildeAmp:    // reduction NAND
    case TokenKind::kTildePipe:   // reduction NOR
    case TokenKind::kEqEq:        // logical equality
    case TokenKind::kBangEq:      // logical inequality
    case TokenKind::kAmpAmp:      // logical AND
    case TokenKind::kPipePipe:    // logical OR
    case TokenKind::kBang:        // logical NOT
      return true;
    default:
      return false;
  }
}

// §30.4.4.1: recursively validates a state-dependent path conditional
// expression. Every operator must be one of the Table 30-1 forms, and every
// identifier operand must be a permitted signal: an input or inout port (or a
// bit-/part-select of one), a locally defined net or variable, or a compile-
// time constant (specparam or literal). An output port is not among the
// permitted operands. Unknown identifiers (module parameters, hierarchical
// names) are left alone so the check only flags what it can prove illegal.
void CheckConditionExpr(const Expr* e, SourceLoc loc, const PortMap& port_map,
                        DiagEngine& diag) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      auto it = port_map.find(e->text);
      if (it != port_map.end() && it->second->direction == Direction::kOutput) {
        diag.Error(loc, std::format("state-dependent path condition operand "
                                    "'{}' may not be an output port",
                                    e->text));
      }
      return;
    }
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      if (!IsAllowedConditionOp(e->op)) {
        diag.Error(loc,
                   "operator is not permitted in a state-dependent path "
                   "conditional expression");
      }
      CheckConditionExpr(e->lhs, loc, port_map, diag);
      return;
    case ExprKind::kBinary:
      if (!IsAllowedConditionOp(e->op)) {
        diag.Error(loc,
                   "operator is not permitted in a state-dependent path "
                   "conditional expression");
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
    case ExprKind::kAssignmentPattern:
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

// Validates the conditional expression of one state-dependent path declaration;
// items without a condition (or non-path items) are ignored.
void CheckItemConditionExpr(const SpecifyItem* si, const PortMap& port_map,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  if (si->path.condition == nullptr) return;
  CheckConditionExpr(si->path.condition, si->loc, port_map, diag);
}

// Pass: enforce the §30.4.4.1 operand and operator rules on every state-
// dependent path conditional expression.
void ValidateConditionExprs(const ModuleDecl* mod, const PortMap& port_map,
                            DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckItemConditionExpr(si, port_map, diag);
    }
  }
}

// §30.7.1: a path-specific PATHPULSE$in$out specparam names module-path input
// and output terminals, which must obey the same direction rules as an ordinary
// module path (§30.4.1): the input terminal shall be an input or inout port and
// the output terminal an output or inout port. A terminal that is provably the
// wrong direction (a declared port of the opposite direction) is rejected; an
// unrecognized name is left alone, matching the conservative style of the other
// specify checks. The bit-/part-select restriction of §30.7.1 needs no check
// here: a select terminates the specparam identifier, so the parser never forms
// such a PATHPULSE$ name. A non-path-specific PATHPULSE$ names no terminals.
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
                           si->pathpulse_input));
  }
  auto out_it = port_map.find(si->pathpulse_output);
  if (out_it != port_map.end() &&
      out_it->second->direction == Direction::kInput) {
    diag.Error(si->loc,
               std::format("PATHPULSE$ output terminal '{}' must be an output "
                           "or inout port",
                           si->pathpulse_output));
  }
}

// Pass: enforce the §30.4.1 terminal-direction rules on every path-specific
// PATHPULSE$ pulse-control specparam (§30.7.1).
void ValidatePulseControlTerminals(const ModuleDecl* mod,
                                   const PortMap& port_map, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckPulseControlTerminals(si, port_map, diag);
    }
  }
}

// Runs all specify-block validation passes for a single module/interface/

}  // namespace delta
