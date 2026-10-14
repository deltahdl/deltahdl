#include "elaborator/coverage_option_rules.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/covergroup_expression_rules.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

// §19.10: the members of a covergroup's `option` structure. A coverpoint's and
// a cross's hold some of them.
constexpr std::array<std::string_view, 11> kOptionMembers = {
    "name",
    "weight",
    "goal",
    "comment",
    "at_least",
    "auto_bin_max",
    "cross_num_print_missing",
    "cross_retain_auto_bins",
    "detect_overlap",
    "per_instance",
    "get_inst_coverage"};

// §19.10: the members of a covergroup's `type_option` structure. A
// coverpoint's and a cross's hold some of them.
constexpr std::array<std::string_view, 7> kTypeOptionMembers = {
    "weight",           "goal",         "comment", "strobe", "merge_instances",
    "distribute_first", "real_interval"};

// §19.10: a coverage option names a member of its structure.
void CheckMember(const CoverageOption& option, DiagEngine& diag) {
  if (IsCovergroupOptionMember(option.member, option.is_type_option)) return;
  diag.Error(option.loc,
             std::format("{} has no member '{}'",
                         option.is_type_option ? "type_option" : "option",
                         option.member),
             Subclause("19.10"));
}

// §19.7, Table 19-1, and §19.7.1, Table 19-3: a weight is a non-negative
// integral value.
void CheckWeight(const CoverageOption& option, DiagEngine& diag) {
  if (option.member != "weight" || option.value == nullptr) return;
  std::optional<int64_t> weight = ConstEvalInt(option.value);
  if (!weight.has_value() || *weight >= 0) return;
  diag.Error(option.value->range.start,
             std::format("the weight {} is negative; a weight is a "
                         "non-negative integral value",
                         *weight),
             Subclause("19.7"));
}

// §19.7.1: a call in a type option's value is a constant one: a constant
// system function, or a function reading no variable outside it that is no
// constant.
void CheckTypeOptionCalls(const Expr* e, const CoverageOption& option,
                          const CovergroupContext& ctx, DiagEngine& diag) {
  if (e == nullptr) return;
  bool non_constant = false;
  if (e->kind == ExprKind::kSystemCall) {
    non_constant = !IsConstantSysFunc(e->callee);
  } else if (e->kind == ExprKind::kCall) {
    const ModuleItem* fn = ctx.function_named(e->callee);
    non_constant = fn != nullptr && !NonConstantReadOutside(*fn, ctx).empty();
  }
  if (non_constant) {
    diag.Error(e->range.start,
               std::format("type option '{}' is set with a call of '{}', "
                           "which is no constant function call",
                           option.member, e->callee),
               Subclause("19.7.1"));
  }
  ForEachExprChild(e, [&](const Expr* child) {
    CheckTypeOptionCalls(child, option, ctx, diag);
  });
}

// §19.7.1: a type option is set with a constant expression.
void CheckTypeOptionValue(const CoverageOption& option,
                          const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag) {
  if (!option.is_type_option || option.value == nullptr) return;
  std::vector<const Expr*> reads;
  CollectBareIdents(option.value, reads);
  for (const Expr* read : reads) {
    if (FindCovergroupFormal(cg, read->text) != nullptr ||
        !ctx.non_constant(read->text)) {
      continue;
    }
    diag.Error(read->range.start,
               std::format("type option '{}' is set with '{}', which is no "
                           "constant",
                           option.member, read->text),
               Subclause("19.7.1"));
  }
  CheckTypeOptionCalls(option.value, option, ctx, diag);
}

void CheckOption(const CoverageOption& option, const CovergroupDecl& cg,
                 const CovergroupContext& ctx, DiagEngine& diag) {
  CheckMember(option, diag);
  CheckWeight(option, diag);
  CheckTypeOptionValue(option, cg, ctx, diag);
}

// The options of a coverpoint's or a cross's body, added to `options`.
void CollectItemOptions(const CoverageSpecOrOption& item,
                        std::vector<const CoverageOption*>& options) {
  if (item.kind == CoverageSpecKind::kCoverPoint) {
    for (const BinsOrOptions& bins : item.cover_point->bins) {
      if (bins.kind == BinsOrOptionsKind::kOption) {
        options.push_back(&bins.option);
      }
    }
  } else if (item.kind == CoverageSpecKind::kCoverCross) {
    for (const CrossBodyItem& body : item.cover_cross->body) {
      if (body.kind == CrossBodyItemKind::kOption) {
        options.push_back(&body.option);
      }
    }
  }
}

}  // namespace

bool IsCovergroupOptionMember(std::string_view member, bool type_option) {
  if (type_option) {
    return std::ranges::find(kTypeOptionMembers, member) !=
           kTypeOptionMembers.end();
  }
  return std::ranges::find(kOptionMembers, member) != kOptionMembers.end();
}

void CheckCoverageOptions(const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag) {
  std::vector<const CoverageOption*> options;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kOption) {
      options.push_back(&item.option);
    } else {
      CollectItemOptions(item, options);
    }
  }
  for (const CoverageOption* option : options) {
    CheckOption(*option, cg, ctx, diag);
  }
}

}  // namespace delta
