#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/gen_block_members.h"
#include "elaborator/pending_generate.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

static bool ExprReferencesName(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprReferencesName(e->lhs, name)) return true;
  if (ExprReferencesName(e->rhs, name)) return true;
  for (const auto* a : e->args) {
    if (ExprReferencesName(a, name)) return true;
  }
  return false;
}

static std::string_view GenvarIterationName(const Stmt* step) {
  if (step->kind == StmtKind::kBlockingAssign) return step->lhs->text;
  return step->expr->lhs->text;
}

static bool ExprHasXZLiteral(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIntegerLiteral) {
    std::string_view text = e->text;
    if (text.find('\'') == std::string_view::npos) return false;
    for (char c : text) {
      if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
    }
    return false;
  }
  return ExprHasXZLiteral(e->lhs) || ExprHasXZLiteral(e->rhs);
}

static std::optional<std::string_view> ValidateGenerateForHeader(
    DiagEngine& diag, const ModuleItem* item) {
  auto genvar_name = item->gen_init->lhs->text;

  if (ExprReferencesName(item->gen_init->rhs, genvar_name)) {
    diag.Error(item->loc,
               "generate-for init reads the loop's own genvar on its "
               "right-hand side",
               Subclause("27.4"));
    return std::nullopt;
  }

  if (GenvarIterationName(item->gen_step) != genvar_name) {
    diag.Error(item->loc, "generate-for init and step assign different genvars",
               Subclause("27.4"));
    return std::nullopt;
  }

  if (ExprHasXZLiteral(item->gen_init->rhs)) {
    diag.Error(item->loc,
               "generate-for genvar must hold no x or z bit while the loop is "
               "evaluated, and the initialization assignment sets one",
               Subclause("27.4"));
    return std::nullopt;
  }
  return genvar_name;
}

static std::optional<int64_t> ComputeIncDecNextValue(
    const Expr* e, const ScopeMap& loop_scope) {
  if (e->kind != ExprKind::kUnary && e->kind != ExprKind::kPostfixUnary) {
    return std::nullopt;
  }
  if (!e->lhs || e->lhs->kind != ExprKind::kIdentifier) return std::nullopt;
  auto it = loop_scope.find(e->lhs->text);
  if (it == loop_scope.end()) return std::nullopt;
  if (e->op == TokenKind::kPlusPlus) return it->second + 1;
  if (e->op == TokenKind::kMinusMinus) return it->second - 1;
  return std::nullopt;
}

static std::optional<int64_t> ComputeGenerateForNextValue(
    DiagEngine& diag, const ModuleItem* item, const ScopeMap& loop_scope) {
  if (item->gen_step->rhs) {
    auto next = ConstEvalInt(item->gen_step->rhs, loop_scope);
    if (!next) {
      diag.Error(item->loc, "generate-for iteration expression is not constant",
                 Subclause("27.4"));
    }
    return next;
  }
  if (item->gen_step->expr) {
    return ComputeIncDecNextValue(item->gen_step->expr, loop_scope);
  }
  return std::nullopt;
}

static bool RegisterGenerateForArrayName(
    DiagEngine& diag, const ModuleItem* item, std::string_view scoped_name,
    const RtlirModule* mod,
    std::unordered_set<std::string_view>& declared_names) {
  if (item->name.empty()) return true;
  if (IsNameDeclared(scoped_name, mod) ||
      !declared_names.insert(scoped_name).second) {
    diag.Error(item->loc,
               std::format("generate block array '{}' conflicts with an "
                           "existing declaration in the same scope",
                           item->name),
               Subclause("27.4"));
    return false;
  }
  return true;
}

static bool GenerateForStepHasXZLiteral(const ModuleItem* item) {
  return ExprHasXZLiteral(item->gen_step->rhs) ||
         ExprHasXZLiteral(item->gen_step->expr);
}

static std::optional<bool> GenerateForConditionHolds(
    const ModuleItem* item, const ScopeMap& loop_scope) {
  auto cond = ConstEvalInt(item->gen_cond, loop_scope);
  if (!cond) return std::nullopt;
  return *cond != 0;
}

static bool GenerateForGenvarRepeats(DiagEngine& diag, const ModuleItem* item,
                                     int64_t genvar_value,
                                     std::unordered_set<int64_t>& seen_values) {
  if (seen_values.insert(genvar_value).second) return false;
  diag.Error(item->loc,
             "generate-for genvar value is repeated during evaluation",
             Subclause("27.4"));
  return true;
}

static bool AdvanceGenerateForGenvar(DiagEngine& diag, const ModuleItem* item,
                                     std::string_view genvar_name,
                                     ScopeMap& loop_scope) {
  if (GenerateForStepHasXZLiteral(item)) {
    diag.Error(item->loc,
               "generate-for genvar must hold no x or z bit while the loop is "
               "evaluated, and the iteration assignment sets one",
               Subclause("27.4"));
    return false;
  }
  std::optional<int64_t> next =
      ComputeGenerateForNextValue(diag, item, loop_scope);
  if (!next) return false;
  BindDeclaredConstant(loop_scope, genvar_name, *next);
  return true;
}

std::optional<Elaborator::GenerateForOpening> Elaborator::OpenGenerateForLoop(
    ModuleItem* item, RtlirModule* mod, const ScopeMap& scope) {
  auto genvar_name_opt = ValidateGenerateForHeader(diag_, item);
  if (!genvar_name_opt) return std::nullopt;
  auto genvar_name = *genvar_name_opt;

  if (active_loop_genvars_.count(genvar_name)) {
    diag_.Error(item->loc,
                std::format("genvar '{}' is already in use by an enclosing "
                            "loop generate construct",
                            genvar_name),
                Subclause("27.4"));
    return std::nullopt;
  }

  if (!RegisterGenerateForArrayName(diag_, item, ScopedName(item->name), mod,
                                    declared_names_)) {
    return std::nullopt;
  }

  auto init_val = ConstEvalInt(item->gen_init->rhs, scope);
  if (!init_val) {
    diag_.Error(item->loc, "generate-for init is not constant",
                Subclause("27.4"));
    return std::nullopt;
  }
  return GenerateForOpening{genvar_name, *init_val};
}

void Elaborator::ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                                      const ScopeMap& scope) {
  auto opening = OpenGenerateForLoop(item, mod, scope);
  if (!opening) return;
  auto genvar_name = opening->genvar_name;

  ScopeMap loop_scope = scope;
  BindDeclaredConstant(loop_scope, genvar_name, opening->init_value);
  std::string saved_prefix = gen_prefix_;
  active_loop_genvars_.insert(genvar_name);
  LocalNameFrame genvar_names(genvar_name);

  size_t const_depth = gen_loop_consts_.size();
  gen_loop_consts_.emplace_back(genvar_name, opening->init_value);
  gen_block_path_.push_back(
      {item->name_is_generated ? std::string_view{} : item->name,
       true,
       opening->init_value,
       item->name,
       {}});
  gen_prefix_scopes_.emplace_back();

  auto close_loop = [&] {
    gen_prefix_ = saved_prefix;
    active_loop_genvars_.erase(genvar_name);
    gen_loop_consts_.resize(const_depth);
    gen_block_path_.pop_back();
    gen_prefix_scopes_.pop_back();
  };

  std::unordered_set<int64_t> seen_values;

  int64_t iter = 0;
  for (; iter < max_generate_iterations_; ++iter) {
    std::optional<bool> keep_iterating =
        GenerateForConditionHolds(item, loop_scope);
    if (!keep_iterating) {
      diag_.Error(item->loc,
                  "generate-for termination expression is not constant",
                  Subclause("27.4"));
      close_loop();
      return;
    }
    if (!*keep_iterating) break;

    if (GenerateForGenvarRepeats(diag_, item, loop_scope[genvar_name],
                                 seen_values)) {
      close_loop();
      return;
    }

    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, item->name,
                              loop_scope[genvar_name]);
    gen_prefix_scopes_.back() = InternedGenPrefix();
    gen_loop_consts_[const_depth].second = loop_scope[genvar_name];
    EnterLoopBlockInstance(mod, gen_block_path_, genvar_name,
                           loop_scope[genvar_name]);
    ElaborateGenerateItems(item->gen_body, mod, loop_scope);

    if (!AdvanceGenerateForGenvar(diag_, item, genvar_name, loop_scope)) {
      close_loop();
      return;
    }
  }

  if (iter == max_generate_iterations_) {
    diag_.Error(item->loc,
                std::format("loop generate scheme did not terminate within {} "
                            "iterations",
                            max_generate_iterations_),
                Subclause("27.4"));
  }

  close_loop();
}

}  // namespace delta
