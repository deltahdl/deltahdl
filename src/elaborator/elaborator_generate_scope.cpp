#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

bool IsConditionalGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf || k == ModuleItemKind::kGenerateCase;
}

bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
                           bool has_begin_end) {
  return !has_begin_end && body.size() == 1 &&
         IsConditionalGenerateConstruct(body[0]->kind);
}

void Elaborator::ElaborateConditionalGenerateBlock(
    const ConditionalGenerateBlock& block, RtlirModule* mod,
    const ScopeMap& scope) {
  if (IsDirectlyNestedBlock(block.body, block.has_begin_end)) {
    ElaborateGenerateItems(block.body, mod, scope);
    return;
  }
  std::string saved_prefix = gen_prefix_;
  gen_prefix_ = std::format("{}{}_", saved_prefix, block.name);
  gen_prefix_scopes_.push_back(InternedGenPrefix());
  gen_block_path_.push_back(
      {block.name_is_generated ? std::string_view{} : block.name,
       false,
       0,
       block.name,
       {}});
  mod->gen_block_instances.push_back(gen_block_path_);
  ElaborateGenerateItems(block.body, mod, scope);
  gen_block_path_.pop_back();
  gen_prefix_scopes_.pop_back();
  gen_prefix_ = saved_prefix;
}

void Elaborator::ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                                     const ScopeMap& scope) {
  auto cond = EvalConstTypeRefCompare(item->gen_cond, mod);
  if (!cond) cond = ConstEvalInt(item->gen_cond, scope);
  if (!cond) {
    diag_.Error(item->loc, "generate-if condition is not constant",
                Subclause("27.5"));
    return;
  }
  if (*cond) {
    ElaborateConditionalGenerateBlock(
        {item->name, item->name_is_generated, item->gen_body,
         item->gen_body_has_begin_end},
        mod, scope);
    return;
  }
  if (item->gen_else == nullptr) return;

  if (item->gen_else->gen_cond != nullptr) {
    ElaborateGenerateIf(item->gen_else, mod, scope);
    return;
  }
  ElaborateConditionalGenerateBlock(
      {item->gen_else->name, item->gen_else->name_is_generated,
       item->gen_else->gen_body, item->gen_else->gen_body_has_begin_end},
      mod, scope);
}

static bool CaseItemsAreConstant(DiagEngine& diag, const ModuleItem& item,
                                 const ScopeMap& scope) {
  bool all_constant = true;
  for (const auto& ci : item.gen_case_items) {
    for (const auto* pat : ci.patterns) {
      if (ConstEvalInt(pat, scope)) continue;
      diag.Error(pat->range.start,
                 "generate-case item expression is not constant",
                 Subclause("27.3"));
      all_constant = false;
    }
  }
  return all_constant;
}

static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  return std::any_of(patterns.begin(), patterns.end(), [&](const Expr* pat) {
    return ConstEvalInt(pat, scope) == selector;
  });
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  const bool kTypeSelector =
      ResolveTypeRefOperandArray(item->gen_cond, mod).has_value();
  std::optional<int64_t> selector;
  if (!kTypeSelector) selector = ConstEvalInt(item->gen_cond, scope);
  if (!kTypeSelector && !selector) {
    diag_.Error(item->loc, "generate-case selector is not constant",
                Subclause("27.5"));
    return;
  }
  if (!kTypeSelector && !CaseItemsAreConstant(diag_, *item, scope)) return;
  auto matches = [&](const std::vector<Expr*>& patterns) {
    if (!kTypeSelector) return MatchesCasePattern(patterns, *selector, scope);
    return std::any_of(patterns.begin(), patterns.end(), [&](const Expr* p) {
      return TypeRefsMatch(item->gen_cond, p, mod).value_or(false);
    });
  };
  const GenerateCaseItem* default_item = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_item = &ci;
      continue;
    }
    if (matches(ci.patterns)) {
      ElaborateConditionalGenerateBlock(
          {ci.label, ci.name_is_generated, ci.body, ci.has_begin_end}, mod,
          scope);
      return;
    }
  }
  if (default_item == nullptr) return;
  ElaborateConditionalGenerateBlock(
      {default_item->label, default_item->name_is_generated, default_item->body,
       default_item->has_begin_end},
      mod, scope);
}

void Elaborator::ElaborateGenerateBlockImport(ModuleItem* item,
                                              RtlirModule* mod) {
  size_t recorded = mod->imports.size();
  ElaborateGenerateBlockItem(item, mod);
  if (mod->imports.size() == recorded) return;
  std::string scope =
      std::format("{}:import{}:", gen_prefix_, mod->imports.size());
  std::string_view interned{arena_.AllocString(scope.c_str(), scope.size()),
                            scope.size()};
  mod->imports.back().scope_prefix = interned;
  auto step = gen_prefix_scopes_.empty() ? gen_prefix_scopes_.end()
                                         : gen_prefix_scopes_.end() - 1;
  gen_prefix_scopes_.insert(step, interned);
}

}  // namespace delta
