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
  // §23.9 judges a declaration against the scope it is written in, and a
  // generate block's enclosing scope is the module Elaborator::ElaborateModule
  // has already returned from. Install that module's names, which
  // Elaborator::ElaborateModule captured into module_declared_names_ before
  // ItemElaborationStateSaver::Restore took them out of declared_names_.
  auto saved_declared_names = std::move(declared_names_);
  declared_names_ = std::move(module_declared_names_[pg.mod]);
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
  // Write what this generate declared back into the module's entry rather than
  // dropping it. §27.4 puts two generate block instance arrays of one module in
  // one scope, so a name one generate construct of a module declared has to be
  // visible to the next generate construct of the same module; each is a
  // separate entry in pending_generates_, so a snapshot taken per entry would
  // hide the first from the second.
  //
  // The entry is looked up by key again rather than held in a reference across
  // the switch above. Elaborating a generate block reaches
  // Elaborator::ElaborateModuleInst and so re-enters
  // Elaborator::ElaborateModule for a module instantiated inside the block,
  // which inserts into module_declared_names_ and can rehash it, and a
  // reference taken before that would dangle.
  module_declared_names_[pg.mod] = std::move(declared_names_);
  declared_names_ = std::move(saved_declared_names);
}

// Stamp one generate block instance's loop-index values and name prefix onto
// everything appended to `items` at or after index `first`. Every vector an
// item can append to is stamped the same way, so this states the rule once and
// each vector is one call: a vector added to RtlirModule later needs a call
// added here and nothing else. RtlirModule::udp_insts is the vector that went
// unstamped when it was added, which left each instance of a loop body with an
// empty prefix and no genvar binding.
template <typename Item>
static void StampGenBlockInstance(std::vector<Item>& items, size_t first,
                                  const GenBlockConsts& consts,
                                  GenBlockPrefix prefix) {
  for (size_t i = first; i < items.size(); ++i) {
    items[i].gen_block_consts = consts;
    items[i].gen_block_prefix = prefix;
  }
}

// §27.4: what an ordinary item elaborates to belongs to one instance of the
// generate block, but every instance shares the one body AST. Stamp this
// instance's loop-index values onto whatever the item produced, which is the
// only place the instances can still be told apart. A process, a continuous
// assignment and a user-defined primitive instance each reach simulation as
// their own thread, and the clause admits the parameter "anywhere within the
// generate block that a normal parameter with an integer value can be used", so
// all three carry it. Lowerer::LowerUdpInst in src/simulator/lowerer_udp.cpp
// gives an RtlirUdpInst a Process of its own for the reason
// Lowerer::LowerContAssign in src/simulator/lowerer_contassign.cpp gives one to
// an RtlirContAssign, which is why RtlirUdpInst carries the same two members as
// RtlirContAssign.
//
// The block's own declarations are named under the generate prefix while the
// shared body still calls them by their simple names, so the prefix rides along
// for the same reason and by the same route.
void Elaborator::ElaborateGenerateBlockItem(ModuleItem* item,
                                            RtlirModule* mod) {
  size_t first_proc = mod->processes.size();
  size_t first_assign = mod->assigns.size();
  size_t first_udp = mod->udp_insts.size();
  ElaborateItem(item, mod);
  GenBlockPrefix prefix = InternedGenPrefix();
  StampGenBlockInstance(mod->processes, first_proc, gen_loop_consts_, prefix);
  StampGenBlockInstance(mod->assigns, first_assign, gen_loop_consts_, prefix);
  StampGenBlockInstance(mod->udp_insts, first_udp, gen_loop_consts_, prefix);
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
      case ModuleItemKind::kDefparam:
        // §23.10.1: a defparam belongs to the block instance it was written in,
        // and Elaborator::ApplyDefparams reads ModuleDecl::items, which holds
        // only a module's own. Record it here rather than descending the AST
        // from there, because this runs for the blocks §27.5 instantiated into
        // the model and for no others, so an alternative that was not selected
        // contributes nothing without having to be recognised as unselected.
        // The prefix and the loop-index bindings are captured now because both
        // are properties of this instance, and the shared body AST records
        // neither.
        generate_defparams_[mod].push_back(
            {item, InternedGenPrefix(), gen_loop_consts_, gen_block_path_});
        break;
      default:
        ElaborateGenerateBlockItem(item, mod);
        break;
    }
  }
  gen_const_scope_ = saved_gen_const_scope;
}

// §27.5: "a conditional generate construct" is the if generate construct and
// the case generate construct, and the clause rules on page 825 that direct
// nesting "applies only to conditional generate constructs nested in
// conditional generate constructs. It does not apply in any way to loop
// generate constructs."
static bool IsConditionalGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf || k == ModuleItemKind::kGenerateCase;
}

// §27.5: "If a generate block in a conditional generate construct consists of
// only one item that is itself a conditional generate construct and if that
// item is not surrounded by begin-end keywords, then this generate block is not
// treated as a separate scope. The generate construct within this block is said
// to be directly nested. The generate blocks of the directly nested construct
// are treated as if they belong to the outer construct."
static bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
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
  gen_block_path_.push_back(
      {block.name_is_generated ? std::string_view{} : block.name, false, 0});
  ElaborateGenerateItems(block.body, mod, scope);
  gen_block_path_.pop_back();
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

static bool IsGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf ||
         k == ModuleItemKind::kGenerateFor ||
         k == ModuleItemKind::kGenerateCase;
}

// §27.6: "All unnamed generate blocks will be given the name genblk<n> where
// <n> is the number assigned to its enclosing generate construct. If such a
// name would conflict with an explicitly declared name, then leading zeros are
// added in front of the number until the name does not conflict."
static std::string_view GenerateBlockName(
    int64_t n, const std::unordered_set<std::string_view>& used, Arena& arena) {
  std::string digits = std::to_string(n);
  std::string candidate = "genblk" + digits;
  while (used.count(candidate)) {
    digits.insert(digits.begin(), '0');
    candidate = "genblk" + digits;
  }
  auto* buf = arena.AllocString(candidate.c_str(), candidate.size());
  return {buf, candidate.size()};
}

// Declared here because NameConstructBlocks and NameGenerateBlocksInScope call
// each other: a scope numbers the constructs it holds, and a construct's blocks
// are each a scope in their own right.
static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena);

// §27.6: "Each generate construct in a given scope is assigned a number. The
// number will be 1 for the construct that appears textually first in that
// scope and will increase by 1 for each subsequent generate construct in that
// scope." A construct that carries a name still takes a number, which is why
// the standard's own example names the construct written after `begin : g1`
// genblk4 rather than genblk3.
//
// The count restarts in each scope, so this recurses into the body of every
// construct it numbers. §27.4 rules that a generate block "comprises a
// separate scope and a new level of hierarchy when it is instantiated", and
// §27.6 writes the first nested construct of a block named g1 as
// top.g1[0].genblk1. Each alternative of a conditional construct is walked on
// its own, since only one of them is ever instantiated.
static void NameGenerateBlocksInScope(const std::vector<ModuleItem*>& items,
                                      std::unordered_set<std::string_view> used,
                                      Arena& arena) {
  for (auto* it : items) {
    if (!it->name.empty()) used.insert(it->name);
  }

  // The §27.6 name is computed for every construct and not only for the unnamed
  // ones, because one construct has more than one block and each of them needs
  // the name independently: a named then-block must not stop the unnamed else
  // block beside it from taking the construct's number.
  int64_t n = 0;
  for (auto* it : items) {
    if (!IsGenerateConstruct(it->kind)) continue;
    ++n;
    std::string_view name = GenerateBlockName(n, used, arena);
    used.insert(name);
    NameConstructBlocks(it, name, arena);
  }
}

// Where one generate block's name is written, and where the fact that §27.6
// assigned it rather than the source is recorded beside it. ModuleItem and
// GenerateCaseItem hold the pair under different member names, so it is passed
// rather than the node holding it.
namespace {
struct GenerateBlockNameSlot {
  std::string_view& name;
  bool& is_generated;
};
}  // namespace

// Name one generate block, then walk what it holds. The §27.6 name is recorded
// as assigned, because §23.6 lets a hierarchical name written outside the block
// reach into it only when the source named it.
static void NameGenerateBlock(GenerateBlockNameSlot slot,
                              const std::vector<ModuleItem*>& body,
                              bool has_begin_end, std::string_view name,
                              Arena& arena) {
  if (slot.name.empty()) {
    slot.name = name;
    slot.is_generated = true;
  }
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    NameConstructBlocks(body[0], name, arena);
    return;
  }
  NameGenerateBlocksInScope(body, {}, arena);
}

// Name every block of one construct, and of any construct directly nested in
// it, which §27.5 rules belong to the outer construct and therefore share its
// number rather than taking one of their own.
static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena) {
  if (!IsConditionalGenerateConstruct(it->kind)) {
    // §27.5: direct nesting "does not apply in any way to loop generate
    // constructs", so a loop generate block is a scope whatever it holds.
    if (it->name.empty()) {
      it->name = name;
      it->name_is_generated = true;
    }
    NameGenerateBlocksInScope(it->gen_body, {}, arena);
    return;
  }
  NameGenerateBlock({it->name, it->name_is_generated}, it->gen_body,
                    it->gen_body_has_begin_end, name, arena);
  for (auto& alt : it->gen_case_items) {
    NameGenerateBlock({alt.label, alt.name_is_generated}, alt.body,
                      alt.has_begin_end, name, arena);
  }
  if (it->gen_else == nullptr) return;
  if (it->gen_else->gen_cond != nullptr) {
    NameConstructBlocks(it->gen_else, name, arena);
    return;
  }
  NameGenerateBlock({it->gen_else->name, it->gen_else->name_is_generated},
                    it->gen_else->gen_body,
                    it->gen_else->gen_body_has_begin_end, name, arena);
}

void Elaborator::AssignGenerateBlockNames(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> used;
  for (const auto& port : decl->ports) used.insert(port.name);
  for (const auto& p : decl->params) used.insert(p.first);
  NameGenerateBlocksInScope(decl->items, std::move(used), arena_);
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

// §27.3 gives a loop generate's third header position three forms and no
// others:
//
//   genvar_iteration ::=
//       genvar_identifier assignment_operator genvar_expression
//     | inc_or_dec_operator genvar_identifier
//     | genvar_identifier inc_or_dec_operator
//
// Answer the genvar_identifier the step names, or nullopt where the step is
// none of the three and so names no genvar at all. §27.4 puts the same
// requirement in prose -- "Both the initialization and iteration assignments in
// the loop generate scheme shall assign to the same genvar" -- and a position
// holding `i` or `~i` assigns to nothing, so it breaks that sentence as well as
// the production.
//
// Parser::ParseAssignmentOrExprNoSemi builds StmtKind::kBlockingAssign for both
// `i = i + 1` and `i += 1`, which is why one test covers every
// assignment_operator; it builds StmtKind::kNonblockingAssign for `i <= 1`,
// which is no assignment_operator in Annex A.6.2 and is rejected here.
static std::optional<std::string_view> GenvarIterationName(const Stmt* step) {
  if (!step) return std::nullopt;
  if (step->kind == StmtKind::kBlockingAssign) {
    if (step->lhs && step->lhs->kind == ExprKind::kIdentifier) {
      return step->lhs->text;
    }
    return std::nullopt;
  }
  const auto* e = step->expr;
  if (!e) return std::nullopt;
  if (e->kind != ExprKind::kUnary && e->kind != ExprKind::kPostfixUnary) {
    return std::nullopt;
  }
  if (e->op != TokenKind::kPlusPlus && e->op != TokenKind::kMinusMinus) {
    return std::nullopt;
  }
  if (!e->lhs || e->lhs->kind != ExprKind::kIdentifier) return std::nullopt;
  return e->lhs->text;
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

  auto step_genvar = GenvarIterationName(item->gen_step);
  if (!step_genvar) {
    diag.Error(item->loc,
               "generate-for iteration shall assign to a genvar, increment one "
               "or decrement one",
               Subclause("27.4"));
    return std::nullopt;
  }
  if (*step_genvar != genvar_name) {
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
  // §27.4 indexes this block's instances by the genvar value, so the step is
  // retargeted beside the localparam at the top of every iteration.
  gen_block_path_.push_back(
      {item->name_is_generated ? std::string_view{} : item->name, true,
       opening->init_value});

  auto close_loop = [&] {
    gen_prefix_ = saved_prefix;
    active_loop_genvars_.erase(genvar_name);
    gen_loop_consts_.resize(const_depth);
    gen_block_path_.pop_back();
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

    // §27.4: a named generate block "is a declaration of an array of generate
    // block instances", and "the index values in this array are the values
    // assumed by the genvar during elaboration". What tells one instance from
    // another is therefore the block and the index, and not the genvar: two
    // sibling blocks written over one genvar are two distinct arrays, and
    // §27.4 rules that each comprises "a separate scope", so a declaration in
    // one is a different object from the same-named declaration in the other.
    // Spelling the prefix from genvar_name gave both of them one name.
    // AssignGenerateBlockNames has already given an unnamed block the name
    // §27.6 assigns it, so item->name is set whether or not the source wrote
    // one.
    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, item->name,
                              loop_scope[genvar_name]);
    gen_loop_consts_[const_depth].second = loop_scope[genvar_name];
    gen_block_path_.back().index = loop_scope[genvar_name];
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
