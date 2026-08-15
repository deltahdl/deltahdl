#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §27.5 evaluates a conditional generate's expression "during elaboration",
// which here is after Elaborator::ElaborateModule has returned for every
// module. Install the typedefs_ and cu_param_scope_ that
// Elaborator::ElaborateBehavioralItem captured when it queued this generate, so
// that the condition and the declarations in the selected body read the scope
// of the module the generate was written in. §26.3 makes an imported name
// locally visible only "prior to that point within the current scope", so a
// name some other module imported must not fold here. Restore the two maps
// before returning, because the caller,
// Elaborator::ResolveDefparamsAndGenerates, shares them with
// Elaborator::ApplyDefparamsRecursively and with the type-width table
// FinalizeDesignTail builds, both of which read the design-wide union that
// Elaborator::ElaborateTopModules installed.
void Elaborator::ProcessPendingGenerate(const PendingGenerate& pg) {
  TypedefMap saved_typedefs = std::move(typedefs_);
  ScopeMap saved_cu_param_scope = std::move(cu_param_scope_);
  typedefs_ = pg.typedefs;
  cu_param_scope_ = pg.cu_param_scope;
  auto scope = BuildParamScope(pg.mod);
  switch (pg.item->kind) {
    case ModuleItemKind::kGenerateIf:
      ElaborateGenerateIf(pg.item, pg.mod, scope);
      break;
    case ModuleItemKind::kGenerateCase:
      ElaborateGenerateCase(pg.item, pg.mod, scope);
      break;
    case ModuleItemKind::kGenerateFor:
      ElaborateGenerateFor(pg.item, pg.mod, scope);
      break;
    default:
      break;
  }
  // A typedef the selected body declared was written into typedefs_ by
  // Elaborator::ElaborateTypedef, and §20.6.2 $bits reads its width back off
  // design->type_widths, which FinalizeDesignTail builds from the map restored
  // here. Fold this generate's entries into that map rather than dropping them
  // with the rest of the per-module scope.
  // ItemElaborationStateSaver::RestoreScopeMaps in
  // src/elaborator/elaborator_module.cpp folds a module's entries in for the
  // same reason. Visibility is unaffected: the next pending generate installs
  // its own captured map over this one.
  for (const auto& [name, dtype] : typedefs_)
    saved_typedefs.insert_or_assign(name, dtype);
  typedefs_ = std::move(saved_typedefs);
  cu_param_scope_ = std::move(saved_cu_param_scope);
}

// §27.4: what an ordinary item elaborates to belongs to one instance of the
// generate block, but every instance shares the one body AST. Stamp this
// instance's loop-index values onto whatever the item produced, which is the
// only place the instances can still be told apart. A process and a continuous
// assignment both reach simulation as their own thread, and the clause admits
// the parameter "anywhere within the generate block that a normal parameter
// with an integer value can be used", so both carry it.
//
// The block's own declarations are named under the generate prefix while the
// shared body still calls them by their simple names, so the prefix rides along
// for the same reason and by the same route.
void Elaborator::ElaborateGenerateBlockItem(ModuleItem* item,
                                            RtlirModule* mod) {
  size_t first_proc = mod->processes.size();
  size_t first_assign = mod->assigns.size();
  ElaborateItem(item, mod);
  GenBlockPrefix prefix = InternedGenPrefix();
  for (size_t i = first_proc; i < mod->processes.size(); ++i) {
    mod->processes[i].gen_block_consts = gen_loop_consts_;
    mod->processes[i].gen_block_prefix = prefix;
  }
  for (size_t i = first_assign; i < mod->assigns.size(); ++i) {
    mod->assigns[i].gen_block_consts = gen_loop_consts_;
    mod->assigns[i].gen_block_prefix = prefix;
  }
}

void Elaborator::ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                                        RtlirModule* mod,
                                        const ScopeMap& scope) {
  // §20.10.1: expose the genvar (and any generate-block localparam) bindings in
  // effect for this body to the elaboration severity task's constant-argument
  // check, which otherwise only sees module parameters. Saved/restored so the
  // overlay is empty again once we leave the generate scope.
  ScopeMap saved_gen_const_scope = gen_const_scope_;
  gen_const_scope_ = scope;
  for (auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kGenerateIf:
        ElaborateGenerateIf(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateCase:
        ElaborateGenerateCase(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateFor:
        ElaborateGenerateFor(item, mod, scope);
        break;
      default:
        ElaborateGenerateBlockItem(item, mod);
        break;
    }
  }
  gen_const_scope_ = saved_gen_const_scope;
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
    ElaborateGenerateItems(item->gen_body, mod, scope);
  } else if (item->gen_else) {
    ElaborateGenerateItems(item->gen_else->gen_body, mod, scope);
  }
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
  const std::vector<ModuleItem*>* default_body = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_body = &ci.body;
      continue;
    }
    if (MatchesCasePattern(ci.patterns, *selector, scope)) {
      ElaborateGenerateItems(ci.body, mod, scope);
      return;
    }
  }
  if (default_body) {
    ElaborateGenerateItems(*default_body, mod, scope);
  }
}

static bool IsGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf ||
         k == ModuleItemKind::kGenerateFor ||
         k == ModuleItemKind::kGenerateCase;
}

void Elaborator::AssignGenerateBlockNames(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> used;
  for (const auto& port : decl->ports) used.insert(port.name);
  for (const auto& p : decl->params) used.insert(p.first);
  for (auto* it : decl->items) {
    if (!it->name.empty()) used.insert(it->name);
  }

  int64_t n = 0;
  for (auto* it : decl->items) {
    if (!IsGenerateConstruct(it->kind)) continue;
    ++n;
    if (!it->name.empty()) continue;
    std::string digits = std::to_string(n);
    std::string candidate = "genblk" + digits;
    while (used.count(candidate)) {
      digits.insert(digits.begin(), '0');
      candidate = "genblk" + digits;
    }
    auto* buf = arena_.AllocString(candidate.c_str(), candidate.size());
    it->name = std::string_view(buf, candidate.size());
    used.insert(it->name);
  }
}

// §27.5: gather the block names introduced by the alternatives of a single
// generate construct. An if-generate contributes its then-block name and,
// recursively, the names of every else / else-if alternative; a case-generate
// contributes the label of each case item (including default); a loop generate
// contributes its array name. Names are collected into a set so that the same
// name labelling more than one alternative of one conditional construct counts
// only once -- at most one alternative is ever instantiated, so reusing a name
// across the alternatives of a single conditional construct is permitted.
static void CollectGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items) {
        if (!ci.label.empty()) out.insert(ci.label);
      }
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

// Names of ordinary declarations in this scope: ports, parameters, and the
// named module items that are not themselves generate constructs.
static std::unordered_set<std::string_view> CollectNonGenerateDeclNames(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> decl_names;
  for (const auto& port : decl->ports)
    if (!port.name.empty()) decl_names.insert(port.name);
  for (const auto& p : decl->params)
    if (!p.first.empty()) decl_names.insert(p.first);
  for (const auto* item : decl->items) {
    if (IsGenerateConstruct(item->kind)) continue;
    if (!item->name.empty()) decl_names.insert(item->name);
    if (!item->inst_name.empty()) decl_names.insert(item->inst_name);
    if (!item->gate_inst_name.empty()) decl_names.insert(item->gate_inst_name);
  }
  return decl_names;
}

// How many distinct generate constructs in this scope declare a block of each
// name. A name claimed by more than one construct violates the rule against
// sharing a block name across conditional or loop generate constructs.
static std::unordered_map<std::string_view, int> CountGenerateConstructUses(
    const ModuleDecl* decl) {
  std::unordered_map<std::string_view, int> construct_uses;
  for (const auto* item : decl->items) {
    if (!IsGenerateConstruct(item->kind)) continue;
    std::unordered_set<std::string_view> names;
    CollectGenerateBlockNames(item, names);
    for (auto n : names) ++construct_uses[n];
  }
  return construct_uses;
}

// Report any conditional-generate naming conflicts for the block names declared
// by a single if/case generate construct. A name colliding with an ordinary
// declaration in the same scope, or with a generate block of a different
// construct, is an error; names are deduplicated per construct so that reusing
// one across the alternatives of the same construct is not flagged.
static void ReportConditionalGenerateNameConflicts(
    DiagEngine& diag, const ModuleItem* item,
    const std::unordered_set<std::string_view>& decl_names,
    std::unordered_map<std::string_view, int>& construct_uses) {
  std::unordered_set<std::string_view> names;
  CollectGenerateBlockNames(item, names);
  for (auto n : names) {
    if (decl_names.count(n)) {
      diag.Error(item->loc,
                 std::format("generate block '{}' conflicts with another "
                             "declaration in the same scope",
                             n),
                 Subclause("23.9"));
    } else if (construct_uses[n] > 1) {
      diag.Error(item->loc,
                 std::format("generate block '{}' has the same name as a "
                             "generate block in another generate construct "
                             "in the same scope",
                             n),
                 Subclause("23.9"));
    }
  }
}

// §27.5: enforce the naming rules for conditional generate constructs. A named
// generate block shares the enclosing scope's namespace, so the name of a block
// in an if-generate or case-generate must not also name another declaration in
// that scope, nor a generate block belonging to a different generate construct
// in the same scope. The check looks at every alternative of the construct,
// independent of which one (if any) elaboration selects for instantiation, so a
// collision is reported even when the offending block is not instantiated.
// Reusing a name across the alternatives of one conditional construct is left
// untouched: those names are deduplicated per construct, so only one will be
// counted.
void Elaborator::CheckConditionalGenerateNaming(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> decl_names =
      CollectNonGenerateDeclNames(decl);
  std::unordered_map<std::string_view, int> construct_uses =
      CountGenerateConstructUses(decl);

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGenerateIf &&
        item->kind != ModuleItemKind::kGenerateCase) {
      continue;
    }
    ReportConditionalGenerateNameConflicts(diag_, item, decl_names,
                                           construct_uses);
  }
}

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

static std::string_view StepLhsName(const Stmt* step) {
  if (!step) return {};
  if (step->lhs && step->lhs->kind == ExprKind::kIdentifier) {
    return step->lhs->text;
  }
  if (step->expr) {
    const auto* e = step->expr;
    if ((e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
        e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
      return e->lhs->text;
    }
  }
  return {};
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
  if (!item->gen_init || !item->gen_init->lhs) {
    diag.Warning(item->loc, "malformed generate-for initializer",
                 Subclause("27.4"));
    return std::nullopt;
  }
  auto genvar_name = item->gen_init->lhs->text;

  if (ExprReferencesName(item->gen_init->rhs, genvar_name)) {
    diag.Error(item->loc,
               "generate-for init shall not reference the loop index on the "
               "right-hand side",
               Subclause("27.4"));
    return std::nullopt;
  }

  auto step_lhs = StepLhsName(item->gen_step);
  if (!step_lhs.empty() && step_lhs != genvar_name) {
    diag.Error(item->loc,
               "generate-for init and step shall assign to the same genvar",
               Subclause("27.4"));
    return std::nullopt;
  }

  // §27.4: it shall be an error if any bit of the genvar is set to x or z
  // during evaluation. An x/z initialization value triggers a dedicated
  // error rather than the generic non-constant warning.
  if (ExprHasXZLiteral(item->gen_init->rhs)) {
    diag.Error(item->loc,
               "generate-for genvar shall not have any bit set to x or z "
               "during evaluation, and the initialization assignment sets one",
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
      diag.Warning(item->loc,
                   "generate-for iteration expression is not constant",
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
// where the loop is written, because a generate block "comprises a separate
// scope and a new level of hierarchy when it is instantiated" (§27.4): two
// arrays named alike under different instances of an enclosing loop are
// declared in different scopes and do not conflict, while two written side by
// side under the same instance share a prefix and still do.
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
               Subclause("23.9"));
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
               "generate-for genvar shall not have any bit set to x or z "
               "during evaluation, and the iteration assignment sets one",
               Subclause("27.4"));
    return false;
  }
  std::optional<int64_t> next =
      ComputeGenerateForNextValue(diag, item, loop_scope);
  if (!next) return false;
  loop_scope[genvar_name] = *next;
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
    diag_.Warning(item->loc, "generate-for init is not constant",
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
  loop_scope[genvar_name] = opening->init_value;
  std::string saved_prefix = gen_prefix_;
  active_loop_genvars_.insert(genvar_name);

  // §27.4: open this block's implicit localparam. It shares the loop index's
  // name, and its value in each instance is the index when that instance was
  // elaborated, so the entry is retargeted at the top of every iteration.
  size_t const_depth = gen_loop_consts_.size();
  gen_loop_consts_.emplace_back(genvar_name, opening->init_value);

  auto close_loop = [&] {
    gen_prefix_ = saved_prefix;
    active_loop_genvars_.erase(genvar_name);
    gen_loop_consts_.resize(const_depth);
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
      diag_.Warning(item->loc,
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

    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, genvar_name,
                              loop_scope[genvar_name]);
    gen_loop_consts_[const_depth].second = loop_scope[genvar_name];
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

  // §27.4 states the rule at stake -- "It shall be an error if the loop
  // generate scheme does not terminate" -- so the report names it, and a
  // reader who hit this has somewhere to go. What the report does not say is
  // that the scheme does not terminate, because reaching the bound does not
  // establish that: a scheme that would have stopped at one iteration past it
  // arrives here too. The message names the bound so the two are told apart by
  // the reader the elaborator cannot tell them apart for.
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
