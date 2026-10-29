// The generate blocks a conditional generate construct selects (§27.5), the
// scope each opens, and the step an import written in a block adds to that
// scope (§26.3), moved out of src/elaborator/elaborator_generate.cpp, which
// holds the pending-generate driver, the item walk and the loop generate, at
// its size limit.

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

// §27.5: a conditional generate construct is an if or a case generate
// construct, and the clause rules on page 825 that direct nesting concerns
// conditional generate constructs nested in conditional ones alone and never
// loop generate constructs.
bool IsConditionalGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf || k == ModuleItemKind::kGenerateCase;
}

// §27.5: a generate block of a conditional generate construct whose only item
// is itself a conditional generate construct, written without begin-end, is not
// treated as a separate scope. The generate construct within this block is said
// to be directly nested, and the directly nested construct's generate blocks
// count as the outer construct's.
bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
                           bool has_begin_end) {
  return !has_begin_end && body.size() == 1 &&
         IsConditionalGenerateConstruct(body[0]->kind);
}

// §27.5: elaborate the generate block a conditional generate construct
// selected. A directly nested block is no scope of its own, so its items are
// elaborated under the prefix already in force and no scope is opened for it.
// Otherwise the block creates a scope, named or not -- a named block's name
// declares a generate block instance and names the scope it creates, and an
// unnamed one creates a scope all the same, and AssignGenerateBlockNames has
// already given the unnamed one the name §27.6 assigns it. The block's own name
// is the whole of the scope name: §27.4 gives an index only to a loop generate
// block, whose name declares an array of generate block instances, so a
// conditional generate block contributes its name alone.
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
  // §6.23: a comparison of two type references is a constant expression, so it
  // may gate a generate-if. Fold it here (via §6.22.1 type matching) before the
  // ordinary integer const-eval, which does not understand type-reference
  // operands.
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

  // §27.5: a conditional generate construct picks at most one of its
  // alternative generate blocks by constant expressions evaluated during
  // elaboration, and an `else if` puts one of those expressions on the else
  // branch. Annex A.4.2 gives if_generate_construct ::= if (
  // constant_expression ) generate_block [ else generate_block ], so an
  // `else if` is the else branch taking the bare generate_item alternative of
  // generate_block, and what stands there is a nested if_generate_construct
  // selecting among the alternatives that remain. Elaborate it as one, so that
  // its condition is read.
  //
  // Parser::ParseGenerateIf tells the two forms apart already:
  // src/parser/parser_generate.cpp:181-182 makes gen_else the nested
  // kGenerateIf itself, carrying its own gen_cond, while :184-190 makes a
  // plain else a synthesized kGenerateIf whose gen_cond is null and whose
  // gen_body holds that block's items. Reaching into gen_body for both
  // instantiated the nested then-branch without ever evaluating its
  // condition, so every selector past the first alternative built the wrong
  // block and the final else was unreachable.
  //
  // Recursing opens no scope for the else branch itself, which is what §27.5
  // requires of it: the branch holds one item that is itself a conditional
  // generate construct and no begin-end keywords surround it, so it is directly
  // nested, and the directly nested construct's generate blocks count as the
  // outer construct's.
  if (item->gen_else->gen_cond != nullptr) {
    ElaborateGenerateIf(item->gen_else, mod, scope);
    return;
  }
  ElaborateConditionalGenerateBlock(
      {item->gen_else->name, item->gen_else->name_is_generated,
       item->gen_else->gen_body, item->gen_else->gen_body_has_begin_end},
      mod, scope);
}

// §27.3: every expression of a generate scheme is a constant expression, and
// Syntax 27-1 writes each item expression of a case-generate as one, so every
// item is checked before any is matched, those after the matching one included.
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

// Every pattern folds by the time this runs, CaseItemsAreConstant having
// returned before matching when one does not.
static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  return std::any_of(patterns.begin(), patterns.end(), [&](const Expr* pat) {
    return ConstEvalInt(pat, scope) == selector;
  });
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  // §6.23 (printed page 138): a type reference is a constant usable where a
  // generate case's selector stands, and its items' type references are
  // compared with it by §6.22.1's matching, as `==` compares two of them.
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
  // Hold the default alternative itself rather than its body, because the scope
  // it opens is named by its own label and shaped by its own begin-end
  // keywords, and neither is reachable from the body alone.
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

// §26.3: a wildcard import makes the package's names potentially locally
// visible at a point of the scope only where the import stands before that
// point within the current scope, and an explicit import makes its name
// locally visible from that point on; §27.5 makes the generate block a scope
// of its own. The clause's Example 2 has `initial x = 1; import p2::*;` in a
// block of a module importing p, and the reference binds p::x through the
// enclosing scope because p2's import comes after it, while a reference after
// the import binds p2::x in the block. The import is recorded as the module's
// by ElaborateItem, with a prefix of its own that Lowerer::LowerImports keys
// its names by, and the prefix goes into gen_prefix_scopes_ one step outside
// the block's own so that every item elaborated after it carries it (see
// RtlirImport::scope_prefix); an item elaborated before it was stamped
// without it. The list ends with the block's own prefix wherever an import
// can stand, since the one block that opens no scope, §27.5's directly nested
// one, holds a conditional construct alone; the guard is for that shape.
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
