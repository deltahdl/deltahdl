#include <cstddef>
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
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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
  // §11.5.1 addresses a select on a parameter over the range that parameter
  // was declared with, and §6.16 gives a string parameter characters a
  // concatenation and §6.16.1's len() read back. Both answer from the module
  // installed here, which Elaborator::ElaborateItems installs for the duration
  // of a module's own items. §27.4 makes a generate block "a separate scope
  // and a new level of hierarchy when it is instantiated" and says nothing
  // that would stop either rule at that boundary, so install the same module
  // for the block's items. Without this the folder sees no module at all here:
  // a select is addressed over [width-1:0] and a string operation recovers no
  // characters.
  ParamRangeRegistryGuard param_range_guard(pg.mod);
  // §8.25.1: the same for a constant expression that reads a specialization's
  // parameter through the scope resolution operator, as in `localparam W =
  // C#(4)::p`. The registry is built from the compilation unit rather than
  // from the module, so this is the table Elaborator::ElaborateItems builds
  // and nothing about it had to be captured when the generate was queued.
  std::unordered_map<std::string_view, const ClassDecl*> param_class_registry =
      BuildParamClassRegistry(unit_);
  ParamClassRegistryGuard param_class_guard(&param_class_registry);
  // §13.4.3 has a constant function call "evaluated at elaboration time", and
  // the two guards above do not answer it: the folder reads the function table
  // a ConstFuncRegistryGuard installs. The table is PendingGenerate::func_decls
  // rather than ElaboratorData::func_decls_, because that member is per-module
  // state this site no longer holds. Elaborator::ElaborateItems fills it from
  // the ModuleDecl it is elaborating and ItemElaborationStateSaver puts it back
  // to what it held before that module, so pg.mod's functions are not in it
  // here and a guard opened over it would register a table belonging to no
  // module. Elaborator::ElaborateBehavioralItem copies it onto the entry where
  // pg.mod's own items are what fills it.
  //
  // The copy holds the functions declared among pg.mod's items, which is what
  // RecordTaskFuncNames in src/elaborator/elaborator_items_udp.cpp puts in
  // func_decls_: it walks ModuleDecl::items and does not descend into a
  // generate construct. A function declared inside a generate block is
  // therefore not in this table, and Elaborator::ElaborateGenerateItems adds
  // one to a copy of this table for the duration of the items declaring it.
  //
  // The other four tables Elaborator::ElaborateItems fills from the same
  // ModuleDecl are not copied, because no constant expression reaches them.
  // ElaboratorData::const_names_ is read by Elaborator::ReportConstAssignTarget
  // for §6.20 and by Elaborator::IsNameInModuleScope for §23.9,
  // ElaboratorData::task_names_ by Elaborator::ValidateFunctionBody for §13.4,
  // ElaboratorData::let_names_ by Elaborator::IsNameInModuleScope,
  // ElaboratorData::sequence_names_ by Elaborator::ValidateSequenceEventArgs
  // and Elaborator::IsDeclaredNameForRhs, and
  // ElaboratorData::auto_task_func_names_ by
  // Elaborator::ValidateHierRefToAutomatic for §13.3.1. Every one of those is a
  // check on a name rather than a fold of a value, so each is left to whatever
  // reaches it rather than fixed here.
  ConstFuncRegistryGuard const_func_guard(&pg.func_decls);
  // §16.12: an assertion in the selected body that instantiates a named
  // property or sequence reads property_registry_, per-module state the
  // saver has taken back as it took func_decls_, so the copy the queue site
  // took is installed for the body and the member put back after it.
  PropertyRegistry saved_property_registry = std::move(property_registry_);
  property_registry_ = pg.property_registry;
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
  property_registry_ = std::move(saved_property_registry);
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
                                  const GenBlockPrefixes& prefixes) {
  for (size_t i = first; i < items.size(); ++i) {
    items[i].gen_block_consts = consts;
    items[i].gen_block_prefixes = prefixes;
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
  // §27.4 with §13.4 and §23.6: a subroutine the block declares is a member
  // of this instance's scope, reached from outside by the instance's
  // hierarchical name, and ElaborateItem has just put the one shared
  // declaration in RtlirModule::function_decls under its bare name alone; the
  // record made here is what keeps the instance. §8.24's out-of-block method
  // body is a class's, as RegisterModuleSubroutines in
  // src/simulator/lowerer_register.cpp treats it, and gets no record.
  bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                       item->kind == ModuleItemKind::kTaskDecl;
  if (is_subroutine && item->method_class.empty()) {
    mod->gen_block_subroutines.push_back(
        {item, gen_block_path_, gen_loop_consts_, gen_prefix_scopes_});
  }
  StampGenBlockInstance(mod->processes, first_proc, gen_loop_consts_,
                        gen_prefix_scopes_);
  // §21.2.1.5: the block instances are levels of the name a process
  // reports, so the path is stamped on the processes alone.
  for (size_t i = first_proc; i < mod->processes.size(); ++i) {
    mod->processes[i].gen_block_path = gen_block_path_;
  }
  StampGenBlockInstance(mod->assigns, first_assign, gen_loop_consts_,
                        gen_prefix_scopes_);
  StampGenBlockInstance(mod->udp_insts, first_udp, gen_loop_consts_,
                        gen_prefix_scopes_);
}

// §27.5 (printed page 824) makes a generate block a scope of its own, §23.9
// (printed 761) has a name the block declares locally stand over the
// enclosing scope's, and §6.18 (printed 118) introduces a forward typedef's
// name in the scope it stands in, with the definition to follow in that same
// scope and its basic type conforming to the forward typedef's. The block's
// items are walked with the enclosing scope's tables, so a name the block
// declares as a typedef met the enclosing scope's entry there: the block's
// `typedef struct pair_t;` kept a module pair_t already in the table,
// HandleForwardTypedef in src/elaborator/elaborator_typedef.cpp admitting a
// forward typedef repeated after its own definition, and a function of the
// block between that forward typedef and the definition was resolved at its
// item to the module's one-member pair_t and kept, `g.f(tagged A '{3, 4})`
// reading 30 for §7.2.1's 34; and a nested block's definition stayed in the
// table after the nested block's items, so a function of g written below h
// resolved pair_t to h's three-member one -- both ccc8d1f7f's remainders,
// found by a2d48456a's agent. The enclosing entry of every name a typedef
// item of the block declares, above or below any subroutine, is taken out
// ahead of the walk and handed back for RestoreEnclosingTypedefs to put in
// place once the block's items are done, so the forward typedef installs its
// placeholder over nothing, the definition writes over that, and the
// enclosing scope sees its own entry again below the block. A name the
// enclosing scope has no entry for stays as the block leaves it, since
// Elaborator::ProcessPendingGenerate folds the block's typedefs into the
// design-wide table for §20.6.2's $bits and would find nothing otherwise.
//
// The forward kinds Elaborator::ElaborateTypedef checks a definition against
// take the same trip, and the block's own are erased on the way back: the
// table was written by the block and read by whatever came after it, so a
// block's `typedef struct pair_t;` reached a sibling block's `typedef union
// {...} pair_t;`, written in a scope of its own, and a nested block's
// `typedef enum pair_t;` reached the enclosing block's `typedef struct {...}
// pair_t;` below the nested block, each reported as not conforming to a
// forward typedef of another scope -- b0ea40995's remainder, found by its
// agent. The block's own forward typedef is still recorded over nothing and
// still judges the block's own definition, and the enclosing scope's forward
// kind, back in place below the block, judges the enclosing scope's own
// definition alone. A block declaring no typedef costs nothing here.
struct EnclosingTypedefs {
  // Every name a typedef item of the block declares, forward or definition,
  // which is what the block's walk may have written into the forward kinds.
  std::vector<std::string_view> block_names;
  std::vector<std::pair<std::string_view, DataType>> typedefs;
  std::vector<std::pair<std::string_view, DataTypeKind>> forward_kinds;
};

using ForwardTypedefKinds = std::unordered_map<std::string_view, DataTypeKind>;

template <typename Map>
static void TakeEnclosingEntry(
    std::string_view name, Map& map,
    std::vector<std::pair<std::string_view, typename Map::mapped_type>>&
        taken) {
  auto it = map.find(name);
  if (it == map.end()) return;
  taken.emplace_back(it->first, it->second);
  map.erase(it);
}

static EnclosingTypedefs TakeEnclosingTypedefs(
    const std::vector<ModuleItem*>& items, TypedefMap& typedefs,
    ForwardTypedefKinds& forward_kinds) {
  EnclosingTypedefs taken;
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    taken.block_names.push_back(item->name);
    TakeEnclosingEntry(item->name, typedefs, taken.typedefs);
    TakeEnclosingEntry(item->name, forward_kinds, taken.forward_kinds);
  }
  return taken;
}

static void RestoreEnclosingTypedefs(const EnclosingTypedefs& taken,
                                     TypedefMap& typedefs,
                                     ForwardTypedefKinds& forward_kinds) {
  for (const auto& [name, dtype] : taken.typedefs) {
    typedefs.insert_or_assign(name, dtype);
  }
  for (auto name : taken.block_names) forward_kinds.erase(name);
  for (const auto& [name, kind] : taken.forward_kinds) {
    forward_kinds.insert_or_assign(name, kind);
  }
}

// §27.2 rules that "all other module items, including other generate
// constructs, are allowed in a generate block" once port declarations,
// specify blocks and specparam declarations are excluded, so a function may
// be declared among these items. §13.4.3 has a constant function call
// "evaluated at elaboration time", and the folder answers such a call from
// the table a ConstFuncRegistryGuard installs. RecordTaskFuncNames in
// src/elaborator/elaborator_items_udp.cpp fills the module's table by walking
// ModuleDecl::items and does not descend into a generate construct, so a
// function declared here is in no table until this site puts it in one.
//
// The table installed here is the one already registered, copied and added
// to. §23.9 has the search for a directly referenced identifier "continue
// upward until an item by that name is found or until a module, interface,
// program, or checker boundary is encountered", and a generate block is not
// one of those boundaries, so a call written in a nested block names a
// function of the block enclosing it and a call written in any block names a
// function of the module. A name these items declare overwrites the entry
// they inherited, which is §23.9's identifier "declared locally".
//
// A sibling block names none of them, because the guard puts back what it
// found when these items are done and each block's items are one call to this
// function.
//
// Nothing is installed when these items declare no function, which leaves the
// enclosing table registered and costs a body without functions no copy.
//
// ElaboratorData::task_names_, which RecordTaskFuncNames fills from the same
// walk and which is short of a task declared here for the same reason, is not
// given the same treatment. Elaborator::ValidateFunctionBody reads it to
// enforce §13.4's bar on a function enabling a task, which is a check on a
// name rather than a fold of a value, so it is left to whatever reaches it.
//
// Fills `decls` with the table for these items' walk and answers whether one
// is to be installed at all; moved out of ElaborateGenerateItems, which
// 559f37e6e's forward-kind restore took past the statement threshold.
static bool CollectGenerateBlockFunctions(
    const std::vector<ModuleItem*>& items,
    std::unordered_map<std::string_view, const ModuleItem*>& decls) {
  bool declares_function = false;
  for (const auto* item : items)
    declares_function |= item->kind == ModuleItemKind::kFunctionDecl;
  if (!declares_function) return false;
  if (const auto* outer = RegisteredConstFuncs()) decls = *outer;
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kFunctionDecl) decls[item->name] = item;
  return true;
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
  // §23.9 lists "Generate blocks" among the elements that "define a new
  // scope", so which of the module Elaborator::ProcessPendingGenerate
  // registered the folder may name from here depends on the blocks these items
  // stand in. Every caller sets ElaboratorData::gen_prefix_scopes_ to that
  // before calling, so this is the one site covering the conditional block, the
  // directly nested block that opens no scope of its own, and each iteration of
  // a loop generate block.
  RegisteredGenScopeGuard gen_scope_guard(gen_prefix_scopes_);
  // §26.3: an import these items write is a candidate for the items after it
  // alone, which Elaborator::ElaborateGenerateBlockImport records by adding a
  // step to gen_prefix_scopes_ as the walk reaches it. The steps are the
  // block's and end with its items, so the list is put back as it was found.
  GenBlockPrefixes entry_prefix_scopes = gen_prefix_scopes_;
  // §27.5 with §23.9 and §6.18: the enclosing scope's typedefs and forward
  // typedef kinds for the names these items declare as typedefs, out for the
  // walk and back after it, the block's own forward kinds erased; see
  // TakeEnclosingTypedefs.
  EnclosingTypedefs enclosing_typedefs =
      TakeEnclosingTypedefs(items, typedefs_, forward_typedef_kinds_);
  // §27.2 with §13.4.3 and §23.9: the constant-function table for these
  // items, installed only when they declare a function; see
  // CollectGenerateBlockFunctions.
  std::unordered_map<std::string_view, const ModuleItem*> gen_func_decls;
  std::optional<ConstFuncRegistryGuard> gen_func_guard;
  if (CollectGenerateBlockFunctions(items, gen_func_decls)) {
    gen_func_guard.emplace(&gen_func_decls);
  }
  // §16.15: a generate block with a default disable iff of its own applies
  // it within the block, overriding the enclosing scope's, which is put
  // back after the block's items.
  Expr* enclosing_default_disable_iff = mod->default_disable_iff;
  if (Expr* own = DeclaredDefaultDisableIff(items)) {
    mod->default_disable_iff = own;
  }
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
        generate_defparams_[mod].push_back({item, InternedGenPrefix(),
                                            gen_prefix_scopes_,
                                            gen_loop_consts_, gen_block_path_});
        break;
      case ModuleItemKind::kImportDecl:
        ElaborateGenerateBlockImport(item, mod);
        break;
      default:
        ElaborateGenerateBlockItem(item, mod);
        break;
    }
  }
  // §6.18 (printed page 118) resolves a forward typedef's definition within
  // the same local scope or generate block, before or after the reference,
  // and §27.5 (printed 824) makes the block a scope of its own, so a function
  // the block writes between its own `typedef struct pair_t;` and the
  // structure's definition names pair_t in a formal lawfully. The typedef
  // enters typedefs_ only as the loop above reaches it, after the module's
  // pass in Elaborator::ElaborateItems has run and after ElaborateItem has
  // resolved the function once against the placeholder, so `g.f(tagged A
  // '{3, 4})` read 0 for §7.2.1's 34 -- ca0c213d4's remainder, which reached
  // a block's subroutine with the module's complete table and no block's. The
  // block's subroutines are resolved again here with the table as the walk
  // leaves it, the block's definitions in; the walk descends into a nested
  // construct's blocks, whose subroutines name this block's typedefs through
  // the enclosing scope (§27.3), and a member resolved already resolves to
  // the same type again.
  ResolveModuleSubroutineFormalTypes(items, typedefs_, arena_);
  RestoreEnclosingTypedefs(enclosing_typedefs, typedefs_,
                           forward_typedef_kinds_);
  gen_prefix_scopes_ = std::move(entry_prefix_scopes);
  mod->default_disable_iff = enclosing_default_disable_iff;
  gen_const_scope_ = saved_gen_const_scope;
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
               "generate-for init shall not reference the loop index on the "
               "right-hand side",
               Subclause("27.4"));
    return std::nullopt;
  }

  if (GenvarIterationName(item->gen_step) != genvar_name) {
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
    gen_prefix_scopes_.back() = InternedGenPrefix();
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
