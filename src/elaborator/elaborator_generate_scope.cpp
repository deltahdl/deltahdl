// The generate blocks a conditional generate construct selects (§27.5) and
// the scope each opens, moved out of src/elaborator/elaborator_generate.cpp,
// which holds the pending-generate driver, the item walk and the loop
// generate, at its size limit.

#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

// §27.5: "a conditional generate construct" is the if generate construct and
// the case generate construct, and the clause rules on page 825 that direct
// nesting "applies only to conditional generate constructs nested in
// conditional generate constructs. It does not apply in any way to loop
// generate constructs."
bool IsConditionalGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf || k == ModuleItemKind::kGenerateCase;
}

// §27.5: "If a generate block in a conditional generate construct consists of
// only one item that is itself a conditional generate construct and if that
// item is not surrounded by begin-end keywords, then this generate block is not
// treated as a separate scope. The generate construct within this block is said
// to be directly nested. The generate blocks of the directly nested construct
// are treated as if they belong to the outer construct."
bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
                           bool has_begin_end) {
  return !has_begin_end && body.size() == 1 &&
         IsConditionalGenerateConstruct(body[0]->kind);
}

// §27.5: elaborate the generate block a conditional generate construct
// selected. A directly nested block "is not treated as a separate scope", so
// its items are elaborated under the prefix already in force and no scope is
// opened for it. Otherwise the block creates a scope, named or not -- "If the
// generate block selected for instantiation is named, then this name declares a
// generate block instance and is the name for the scope it creates. If the
// generate block selected for instantiation is not named, it still creates a
// scope", and AssignGenerateBlockNames has already given the unnamed one the
// name §27.6 assigns it. The block's own name is the whole of the scope name:
// §27.4 gives an index only to a loop generate block, whose name "is a
// declaration of an array of generate block instances", so a conditional
// generate block contributes its name alone.
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
      {block.name_is_generated ? std::string_view{} : block.name, false, 0});
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
  auto cond = EvalConstTypeRefCompare(item->gen_cond);
  if (!cond) cond = ConstEvalInt(item->gen_cond, scope);
  if (!cond) {
    diag_.Warning(item->loc, "generate-if condition is not constant",
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

  // §27.5: a conditional generate construct selects "at most one generate
  // block from a set of alternative generate blocks based on constant
  // expressions evaluated during elaboration", and an `else if` puts one of
  // those expressions on the else branch. Annex A.4.2 gives
  // if_generate_construct ::= if ( constant_expression ) generate_block
  // [ else generate_block ], so an `else if` is the else branch taking the
  // bare generate_item alternative of generate_block, and what stands there is
  // a nested if_generate_construct selecting among the alternatives that
  // remain. Elaborate it as one, so that its condition is read.
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
  // nested, and "the generate blocks of the directly nested construct are
  // treated as if they belong to the outer construct".
  if (item->gen_else->gen_cond != nullptr) {
    ElaborateGenerateIf(item->gen_else, mod, scope);
    return;
  }
  ElaborateConditionalGenerateBlock(
      {item->gen_else->name, item->gen_else->name_is_generated,
       item->gen_else->gen_body, item->gen_else->gen_body_has_begin_end},
      mod, scope);
}

static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  for (const auto* pat : patterns) {
    auto val = ConstEvalInt(pat, scope);
    if (val && *val == selector) return true;
  }
  return false;
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  auto selector = ConstEvalInt(item->gen_cond, scope);
  if (!selector) {
    diag_.Warning(item->loc, "generate-case selector is not constant",
                  Subclause("27.5"));
    return;
  }
  // Hold the default alternative itself rather than its body, because the scope
  // it opens is named by its own label and shaped by its own begin-end
  // keywords, and neither is reachable from the body alone.
  const GenerateCaseItem* default_item = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_item = &ci;
      continue;
    }
    if (MatchesCasePattern(ci.patterns, *selector, scope)) {
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

}  // namespace delta
