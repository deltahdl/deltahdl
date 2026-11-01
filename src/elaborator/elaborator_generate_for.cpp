// The loop generate construct (§27.4): its header's checks, the genvar's
// steps and the elaboration of each iteration's block, moved out of
// src/elaborator/elaborator_generate.cpp to keep that file inside the size
// limit assert-no-oversized-source-files enforces.

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

// The genvar_identifier a loop generate's third header position names. A.4.2
// gives genvar_iteration three forms and no others:
//
//   genvar_iteration ::=
//       genvar_identifier assignment_operator genvar_expression
//     | inc_or_dec_operator genvar_identifier
//     | genvar_identifier inc_or_dec_operator
//
// and Parser::ParseGenvarIteration reports a position holding none of them,
// so a step that reaches elaboration has one.
// Parser::ParseAssignmentOrExprNoSemi builds StmtKind::kBlockingAssign for both
// `i = i + 1` and `i += 1`, which is why one test covers every
// assignment_operator; the two inc_or_dec forms are expression statements over
// a unary or postfix-unary node whose operand is the genvar.
static std::string_view GenvarIterationName(const Stmt* step) {
  if (step->kind == StmtKind::kBlockingAssign) return step->lhs->text;
  return step->expr->lhs->text;
}

// §27.4: a genvar value with any bit set to x or z is illegal during loop
// evaluation. Only a based integer literal whose digits include x, z, or ?
// can introduce such a bit, so scan the genvar's init/step expression for
// one (recursing through operands).
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

// §27.4: validate the static form of a generate-for header before any
// iteration. Returns the genvar name when the init/step are well formed (init
// does not reference the loop index, step assigns the same genvar, and the init
// value has no x/z bit); returns nullopt and reports the offending diagnostic
// otherwise.
static std::optional<std::string_view> ValidateGenerateForHeader(
    DiagEngine& diag, const ModuleItem* item) {
  // A.4.2's genvar_initialization names the genvar by an identifier alone, and
  // Parser::ParseGenvarInitialization records it as one.
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

  // §27.4: a genvar that takes an x or z bit at any point of the loop's
  // evaluation is an error. An x/z initialization value triggers a dedicated
  // error rather than the generic non-constant report.
  if (ExprHasXZLiteral(item->gen_init->rhs)) {
    diag.Error(item->loc,
               "generate-for genvar must hold no x or z bit while the loop is "
               "evaluated, and the initialization assignment sets one",
               Subclause("27.4"));
    return std::nullopt;
  }
  return genvar_name;
}

// §27.4: compute the next genvar value for a ++/-- step expression. Returns
// nullopt unless the step is a unary increment/decrement on an identifier that
// is bound in the loop scope.
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

// §27.4: compute the genvar value for the next iteration of a generate-for
// loop. Supports a right-hand-side step expression as well as ++/-- on the
// genvar. Returns nullopt when no valid next value can be determined, which
// terminates the loop.
//
// Report the step expression that does not fold here rather than at the caller,
// because this is the only place that knows why no next value came back. §27.3
// gives `genvar_iteration ::= genvar_identifier assignment_operator
// genvar_expression` and Annex A.8.3 gives `genvar_expression ::=
// constant_expression`, so a right-hand side that does not fold breaks that
// rule and costs the design every instance after the first. The other two ways
// of reaching nullopt break no such rule: a third position holding `i` or `~i`
// is no genvar_iteration at all, and ComputeIncDecNextValue reads only ++ and
// -- on an identifier, so calling either non-constant would name a rule the
// source does not break.
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

// §27.4: a named loop generate block declares an array of generate block
// instances, and it shall be an error if that array's name collides with any
// other declaration in the enclosing scope, including another generate block
// instance array. The array counts as declared even when the loop yields no
// instances, so this check runs before the iteration count is known. Loop
// generate arrays are an error on conflict (unlike conditional generate
// blocks, whose naming rules differ), so the loop path enforces it directly
// rather than through the shared label collector. Returns false (and reports
// the diagnostic) when the array name conflicts; true otherwise.
//
// `scoped_name` is the array name qualified by the generate prefix in force
// where the loop is written, because a generate block forms a scope of its own
// and a further level of hierarchy once instantiated (§27.4): two arrays named
// alike under different instances of an enclosing loop are declared in
// different scopes and do not conflict, while two written side by side under
// the same instance share a prefix and still do.
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

// §27.4: the x/z prohibition holds as the loop advances; a step that drives the
// genvar to an x or z bit is an error, not a silent stop.
static bool GenerateForStepHasXZLiteral(const ModuleItem* item) {
  return ExprHasXZLiteral(item->gen_step->rhs) ||
         ExprHasXZLiteral(item->gen_step->expr);
}

// §27.4: evaluate the generate-for loop condition in the current loop scope.
// Returns true while the loop should keep iterating, false once the condition
// folds to zero, and nullopt when the condition does not fold at all.
//
// The two ways of not iterating are returned apart because only one of them is
// a defect in the source. Annex A.8.3 gives `genvar_expression ::=
// constant_expression`, so a condition that does not fold breaks that rule and
// Elaborator::ElaborateGenerateFor reports it, while a condition that folds to
// zero is the legal zero-trip loop generate and is elaborated in silence. A
// single false answers both, and the design that comes out of the two is the
// same design with no instances in it, so the caller cannot tell them apart
// afterwards.
static std::optional<bool> GenerateForConditionHolds(
    const ModuleItem* item, const ScopeMap& loop_scope) {
  auto cond = ConstEvalInt(item->gen_cond, loop_scope);
  if (!cond) return std::nullopt;
  return *cond != 0;
}

// §27.4: per-iteration genvar validity check, run before elaborating the body
// of one generate-for iteration. Returns true (and reports the diagnostic) when
// the genvar value repeats during evaluation, which must abort the loop. The
// current value is recorded in seen_values so a later repeat can be detected.
static bool GenerateForGenvarRepeats(DiagEngine& diag, const ModuleItem* item,
                                     int64_t genvar_value,
                                     std::unordered_set<int64_t>& seen_values) {
  if (seen_values.insert(genvar_value).second) return false;
  diag.Error(item->loc,
             "generate-for genvar value is repeated during evaluation",
             Subclause("27.4"));
  return true;
}

// §27.4: advance a loop generate's genvar to the value its next iteration runs
// with. Answers false when the loop has to stop, having reported whatever
// stopped it: an iteration assignment driving the genvar to an x or z bit,
// which §27.4 makes an error, or a step expression yielding no next value,
// which ComputeGenerateForNextValue reports where the source breaks a rule.
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

// §27.4: check a loop generate construct's header and open its genvar. Yields
// the genvar name paired with its constant initial value, or nullopt when the
// header is malformed, the generate-block array name clashes, or the init
// expression does not fold.
std::optional<Elaborator::GenerateForOpening> Elaborator::OpenGenerateForLoop(
    ModuleItem* item, RtlirModule* mod, const ScopeMap& scope) {
  auto genvar_name_opt = ValidateGenerateForHeader(diag_, item);
  if (!genvar_name_opt) return std::nullopt;
  auto genvar_name = *genvar_name_opt;

  // Within the generate block the genvar name denotes an implicit localparam
  // that shadows the genvar itself, so it is not possible for a nested loop
  // generate construct to reuse the genvar of an enclosing one -- inside the
  // inner loop that name already refers to the outer block's localparam, not to
  // a genvar (LRM Example 1, mod_a). Sibling loops are fine: each genvar is
  // removed from the active set once its loop finishes.
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

  // §27.4: open this block's implicit localparam. It shares the loop index's
  // name, and its value in each instance is the index when that instance was
  // elaborated, so the entry is retargeted at the top of every iteration.
  size_t const_depth = gen_loop_consts_.size();
  gen_loop_consts_.emplace_back(genvar_name, opening->init_value);
  // §27.4 indexes this block's instances by the genvar value, so the step is
  // retargeted beside the localparam at the top of every iteration.
  gen_block_path_.push_back(
      {item->name_is_generated ? std::string_view{} : item->name,
       true,
       opening->init_value,
       item->name,
       {}});
  // §27.4 puts the index in this block's prefix, so the entry is a different
  // string in every instance and is retargeted at the top of every iteration
  // beside the localparam and the step. It is pushed empty here and read by
  // nothing before the first iteration sets it.
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
    // Report a condition that does not fold, and stop the loop. Annex A.8.3
    // gives `genvar_expression ::= constant_expression`, so such a source is
    // one this run cannot elaborate, and every instance the loop was written
    // to create is missing from the design that comes out. Return rather than
    // break, which keeps the report to one per loop generate construct even
    // though the condition is evaluated once per iteration, and which leaves
    // the iteration count short of max_generate_iterations_ so that a loop
    // stopped for this reason is not also reported as one that never
    // terminates.
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

    // §27.4: a named generate block declares an array of generate block
    // instances indexed by the values the genvar takes during elaboration. What
    // tells one instance from another is therefore the block and the index, and
    // not the genvar: two sibling blocks written over one genvar are two
    // distinct arrays, and §27.4 rules that each forms a scope of its own, so a
    // declaration in one is a different object from the same-named declaration
    // in the other. Spelling the prefix from genvar_name gave both of them one
    // name. AssignGenerateBlockNames has already given an unnamed block the
    // name §27.6 assigns it, so item->name is set whether or not the source
    // wrote one.
    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, item->name,
                              loop_scope[genvar_name]);
    gen_prefix_scopes_.back() = InternedGenPrefix();
    gen_loop_consts_[const_depth].second = loop_scope[genvar_name];
    EnterLoopBlockInstance(mod, gen_block_path_, genvar_name,
                           loop_scope[genvar_name]);
    ElaborateGenerateItems(item->gen_body, mod, loop_scope);

    // Stop the loop when the genvar cannot advance, which
    // AdvanceGenerateForGenvar has already reported. Return rather than break,
    // so that a loop stopped here is not also reported as one that never
    // terminates.
    if (!AdvanceGenerateForGenvar(diag_, item, genvar_name, loop_scope)) {
      close_loop();
      return;
    }
  }

  // §27.4 states the rule at stake -- a loop generate scheme that does not
  // terminate is an error -- so the report names it, and a reader who hit this
  // has somewhere to go. What the report does not say is that the scheme does
  // not terminate, because reaching the bound does not establish that: a scheme
  // that would have stopped at one iteration past it arrives here too. The
  // message names the bound so the two are told apart by the reader the
  // elaborator cannot tell them apart for.
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
