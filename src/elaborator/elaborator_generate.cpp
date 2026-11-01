#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/gen_block_members.h"
#include "elaborator/module_scope_names.h"
#include "elaborator/pending_generate.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

void ElaboratorData::SwapModuleScopeNames(ModuleScopeNames& names) {
  std::swap(declared_names_, names.declared);
  std::swap(net_names_, names.nets);
  std::swap(cont_assign_targets_, names.cont_targets);
  std::swap(proc_assign_targets_, names.proc_targets);
  std::swap(var_init_names_, names.initialized);
  std::swap(uwire_drivers_, names.uwire_drivers);
  std::swap(interconnect_names_, names.interconnects);
  std::swap(force_release_targets_, names.force_targets);
  std::swap(var_types_, names.var_types);
  std::swap(class_var_types_, names.class_var_types);
  std::swap(scalar_var_names_, names.scalar_vars);
  std::swap(real_var_names_, names.real_vars);
  std::swap(real_param_names_, names.real_params);
  std::swap(var_select_shapes_, names.select_shapes);
  std::swap(class_var_names_, names.class_vars);
}

// §27.5 evaluates a conditional generate's expression during elaboration, which
// here is after Elaborator::ElaborateModule has returned for every module.
// Install the typedefs_ and cu_param_scope_ that
// Elaborator::ElaborateBehavioralItem captured when it queued this generate, so
// that the condition and the declarations in the selected body read the scope
// of the module the generate was written in. §26.3 makes an imported name
// locally visible only before that point in the current scope, so a name some
// other module imported must not fold here. Restore the two maps before
// returning, because the caller, Elaborator::ResolveDefparamsAndGenerates,
// shares them with Elaborator::ApplyDefparamsRecursively and with the
// type-width table FinalizeDesignTail builds, both of which read the
// design-wide union that Elaborator::ElaborateTopModules installed.
void Elaborator::ProcessPendingGenerate(const PendingGenerate& pg) {
  TypedefMap saved_typedefs = std::move(typedefs_);
  ScopeMap saved_cu_param_scope = std::move(cu_param_scope_);
  auto saved_td_array_dims = std::move(td_array_dims_);
  typedefs_ = pg.typedefs;
  cu_param_scope_ = pg.cu_param_scope;
  // §3.13 (e): the dimensions of the module's own array typedefs, never those
  // of another design element's typedef of the same name, which the union
  // holds.
  td_array_dims_ = pg.td_array_dims;
  // The block is elaborated after the instance holding it has returned, so
  // the configuration's path to that instance and its library are put back
  // for the instances the block holds (§33.4.1.3, §33.4.1.5).
  std::string saved_config_path =
      std::exchange(config_inst_path_, pg.config_inst_path);
  std::string saved_library = std::exchange(current_library_, pg.library);
  // §23.9 judges a declaration against the scope it is written in, and a
  // generate block's enclosing scope is the module Elaborator::ElaborateModule
  // has already returned from. Install that module's names, which
  // Elaborator::ElaborateModule captured into module_scope_names_ before
  // ItemElaborationStateSaver::Restore took them out of declared_names_.
  ModuleScopeNames enclosing = std::move(module_scope_names_[pg.mod]);
  SwapModuleScopeNames(enclosing);
  // §11.5.1 addresses a select on a parameter over the range that parameter
  // was declared with, and §6.16 gives a string parameter characters a
  // concatenation and §6.16.1's len() read back. Both answer from the module
  // installed here, which Elaborator::ElaborateItems installs for the duration
  // of a module's own items. §27.4 makes a generate block a scope of its own
  // and a further level of hierarchy once instantiated and says nothing that
  // would stop either rule at that boundary, so install the same module for the
  // block's items. Without this the folder sees no module at all here: a select
  // is addressed over [width-1:0] and a string operation recovers no
  // characters.
  ParamRangeRegistryGuard param_range_guard(pg.mod);
  // §20.6.2 with §27.5: `$bits` of a type is a constant expression, and a
  // generate construct's condition, selector or bounds may be one, as may a
  // declaration in the block. The folder sizes the type from the typedef table
  // a TypedefRegistryGuard installs, which Elaborator::ElaborateItems installs
  // for a module's own items, so the same is installed here over the scope put
  // back above. aggregate_typedef_names_ is never taken back between modules,
  // so it already holds this scope's unpacked aggregate names.
  TypedefRegistryGuard typedef_guard(&typedefs_, &aggregate_typedef_names_,
                                     &type_ref_compare_);
  // §8.25.1: the same for a constant expression that reads a specialization's
  // parameter through the scope resolution operator, as in `localparam W =
  // C#(4)::p`. The registry is built from the compilation unit rather than
  // from the module, so this is the table Elaborator::ElaborateItems builds
  // and nothing about it had to be captured when the generate was queued.
  std::unordered_map<std::string_view, const ClassDecl*> param_class_registry =
      BuildParamClassRegistry(unit_);
  ParamClassRegistryGuard param_class_guard(&param_class_registry);
  // §13.4.3 has a constant function call evaluated during elaboration, and the
  // two guards above do not answer it: the folder reads the function table a
  // ConstFuncRegistryGuard installs. The table is PendingGenerate::func_decls
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
  // §25.3 with §23.9: an interface port connection in the body may name the
  // module's interface instances, and those the body itself declares are
  // added as it is elaborated, or reach one through the module's instances,
  // which the module's declaration names.
  auto saved_interface_inst_types =
      std::exchange(interface_inst_types_, pg.interface_inst_types);
  auto saved_decl_path = std::exchange(module_decl_path_, pg.module_decl_path);
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
  // §6.20.4 of the construct's own value parameters, under the guards above
  // and with every instance of its blocks registered on pg.mod.
  ValidateGenerateValueParams(pg.item, pg.mod, scope, unit_, diag_);
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
  td_array_dims_ = std::move(saved_td_array_dims);
  property_registry_ = std::move(saved_property_registry);
  interface_inst_types_ = std::move(saved_interface_inst_types);
  module_decl_path_ = std::move(saved_decl_path);
  config_inst_path_ = std::move(saved_config_path);
  current_library_ = std::move(saved_library);
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
  // which inserts into module_scope_names_ and can rehash it, and a
  // reference taken before that would dangle.
  SwapModuleScopeNames(enclosing);
  module_scope_names_[pg.mod] = std::move(enclosing);
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

// Stamp the generate block instance `path`, with its name prefixes, onto every
// entry appended to `items` at or after index `first`, the scope it stands in.
template <typename Scoped>
static void StampGenBlockScope(std::vector<Scoped>& items, size_t first,
                               const HierPath& path,
                               const GenBlockPrefixes& prefixes) {
  for (size_t i = first; i < items.size(); ++i) {
    items[i].gen_block_path = path;
    items[i].gen_block_prefixes = prefixes;
  }
}

// §27.4: what an ordinary item elaborates to belongs to one instance of the
// generate block, but every instance shares the one body AST. Stamp this
// instance's loop-index values onto whatever the item produced, which is the
// only place the instances can still be told apart. A process, a continuous
// assignment and a user-defined primitive instance each reach simulation as
// their own thread, and the clause admits the parameter anywhere in the
// generate block an ordinary integer parameter may stand, so all three carry
// it, as does a module instance for its port connections. Lowerer::LowerUdpInst
// in src/simulator/lowerer_udp.cpp gives an RtlirUdpInst a Process of its own
// for the reason Lowerer::LowerContAssign in
// src/simulator/lowerer_contassign.cpp gives one to an RtlirContAssign, which
// is why RtlirUdpInst carries the same two members as RtlirContAssign.
//
// The block's own declarations are named under the generate prefix while the
// shared body still calls them by their simple names, so the prefix rides along
// for the same reason and by the same route.
void Elaborator::ElaborateGenerateBlockItem(ModuleItem* item,
                                            RtlirModule* mod) {
  size_t first_proc = mod->processes.size();
  size_t first_assign = mod->assigns.size();
  size_t first_udp = mod->udp_insts.size();
  size_t first_child = mod->children.size();
  size_t first_assertion = mod->assertions.size();
  size_t first_assertion_item = mod->assertion_item_decls.size();
  size_t first_alias = mod->aliases.size();
  ElaborateItem(item, mod);
  ValidateGeneratedItem(item, *mod);
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
  // §37.85 detail 5: a typedef is a typespec of this instance's gen scope.
  if (item->kind == ModuleItemKind::kTypedef) {
    mod->gen_block_typedefs.push_back({item, gen_block_path_});
  }
  StampGenBlockInstance(mod->processes, first_proc, gen_loop_consts_,
                        gen_prefix_scopes_);
  // §21.2.1.5: a process reports the block instances as levels of its name;
  // §37.85, §37.49 and §37.12: an assignment and an assertion the block
  // writes, and a property or sequence it declares, are of this instance.
  StampGenBlockScope(mod->processes, first_proc, gen_block_path_,
                     gen_prefix_scopes_);
  StampGenBlockScope(mod->assigns, first_assign, gen_block_path_,
                     gen_prefix_scopes_);
  StampGenBlockScope(mod->assertions, first_assertion, gen_block_path_,
                     gen_prefix_scopes_);
  StampGenBlockScope(mod->assertion_item_decls, first_assertion_item,
                     gen_block_path_, gen_prefix_scopes_);
  StampGenBlockInstance(mod->assigns, first_assign, gen_loop_consts_,
                        gen_prefix_scopes_);
  StampGenBlockInstance(mod->udp_insts, first_udp, gen_loop_consts_,
                        gen_prefix_scopes_);
  // A module instance's port connections are lowered as continuous
  // assignments (Lowerer::LowerPortBindings), which read the same two.
  StampGenBlockInstance(mod->children, first_child, gen_loop_consts_,
                        gen_prefix_scopes_);
  // §10.11 with §27.5: an alias names the nets of the block it stands in by
  // their simple names, which the block declares under its prefixes.
  for (size_t i = first_alias; i < mod->aliases.size(); ++i) {
    mod->aliases[i].gen_block_prefixes = gen_prefix_scopes_;
  }
}

// §27.5 (printed page 824) makes a generate block a scope of its own, §23.9
// (printed 761) has a name the block declares locally stand over the enclosing
// scope's, and §6.18 (printed 118) introduces a forward typedef's name in the
// scope it stands in, with the definition to follow in that same scope and its
// basic type conforming to the forward typedef's. The block's items are walked
// with the enclosing scope's tables, so a name the block declares as a typedef
// met the enclosing scope's entry there: the block's `typedef struct pair_t;`
// kept a module pair_t already in the table, HandleForwardTypedef in
// src/elaborator/elaborator_typedef.cpp admitting a forward typedef repeated
// after its own definition, and a function of the block between that forward
// typedef and the definition was resolved at its item to the module's
// one-member pair_t and kept, `g.f(tagged A '{3, 4})` reading 30 for §7.2.1's
// 34; and a nested block's definition stayed in the table after the nested
// block's items, so a function of g written below h resolved pair_t to h's
// three-member one -- both ccc8d1f7f's remainders, found by a2d48456a's agent.
// The enclosing entry of every name a typedef item of the block declares, above
// or below any subroutine, is taken out ahead of the walk and handed back for
// RestoreEnclosingTypedefs to put in place once the block's items are done, so
// the forward typedef installs its placeholder over nothing, the definition
// writes over that, and the enclosing scope sees its own entry again below the
// block. A name the enclosing scope has no entry for stays as the block leaves
// it, since Elaborator::ProcessPendingGenerate folds the block's typedefs into
// the design-wide table for §20.6.2's $bits and would find nothing otherwise.
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
//
// §3.13 (f) puts the block's typedefs and classes in the block's name space,
// so the enclosing scope's unpacked dimensions for each name take the same
// trip, and the block's own are erased on the way back. A typedef of the block
// written with none left the module's in the table for the block's variable.
struct EnclosingTypedefs {
  // Every name a typedef or class item of the block declares, forward or
  // definition, which is what the block's walk may have written into the
  // forward kinds and the dimension table.
  std::vector<std::string_view> block_names;
  std::vector<std::pair<std::string_view, DataType>> typedefs;
  std::vector<std::pair<std::string_view, DataTypeKind>> forward_kinds;
  std::vector<std::pair<std::string_view, std::vector<Expr*>>> td_array_dims;
};

using ForwardTypedefKinds = std::unordered_map<std::string_view, DataTypeKind>;
using TypedefDims = std::unordered_map<std::string_view, std::vector<Expr*>>;

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
    ForwardTypedefKinds& forward_kinds, TypedefDims& td_dims) {
  EnclosingTypedefs taken;
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kTypedef &&
        item->kind != ModuleItemKind::kClassDecl)
      continue;
    taken.block_names.push_back(item->name);
    TakeEnclosingEntry(item->name, typedefs, taken.typedefs);
    TakeEnclosingEntry(item->name, forward_kinds, taken.forward_kinds);
    TakeEnclosingEntry(item->name, td_dims, taken.td_array_dims);
  }
  return taken;
}

static void RestoreEnclosingTypedefs(const EnclosingTypedefs& taken,
                                     TypedefMap& typedefs,
                                     ForwardTypedefKinds& forward_kinds,
                                     TypedefDims& td_dims) {
  for (const auto& [name, dtype] : taken.typedefs) {
    typedefs.insert_or_assign(name, dtype);
  }
  for (auto name : taken.block_names) {
    forward_kinds.erase(name);
    td_dims.erase(name);
  }
  for (const auto& [name, kind] : taken.forward_kinds) {
    forward_kinds.insert_or_assign(name, kind);
  }
  for (const auto& [name, dims] : taken.td_array_dims) {
    td_dims.insert_or_assign(name, dims);
  }
}

// §27.5 makes a generate block a scope of its own, and §23.9 lets a name the
// block declares hide one the enclosing scope declares, for the block's items
// and no further. The variable tables are flat, keyed by the simple name, so
// the enclosing scope's entries for the names the block declares are set
// aside while the block's walk writes its own, and the block's are erased and
// the enclosing ones put back when the walk leaves it. A sibling block then
// reads the enclosing scope's again.
template <typename Table>
class ShadowedEntries {
 public:
  ShadowedEntries(Table& table, const std::vector<std::string_view>& names)
      : table_(table), names_(names) {
    for (std::string_view name : names_) {
      auto node = table_.extract(name);
      if (!node.empty()) taken_.insert(std::move(node));
    }
  }
  ShadowedEntries(const ShadowedEntries&) = delete;
  ShadowedEntries& operator=(const ShadowedEntries&) = delete;
  ~ShadowedEntries() {
    for (std::string_view name : names_) table_.erase(name);
    table_.merge(taken_);
  }

 private:
  Table& table_;
  const std::vector<std::string_view>& names_;
  Table taken_;
};

// The names the variable, net and parameter declarations among `items`
// declare.
static std::vector<std::string_view> DeclaredDataNames(
    const std::vector<ModuleItem*>& items) {
  std::vector<std::string_view> names;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl ||
        item->kind == ModuleItemKind::kParamDecl) {
      names.push_back(item->name);
    }
  }
  return names;
}

// §27.2 allows every other module item, other generate constructs included, in
// a generate block once port declarations, specify blocks and specparam
// declarations are excluded, so a function may be declared among these items.
// §13.4.3 has a constant function call evaluated during elaboration, and the
// folder answers such a call from the table a ConstFuncRegistryGuard installs;
// but it also bars a constant function from being declared inside a generate
// block, so a function declared here is entered with no declaration, which the
// folder folds no call of (RegisteredConstFunc) and the validator reports a
// constant-context call of (ValidateConstFuncCallsInBlock).
//
// The table installed here is the one already registered, copied and added
// to. §23.9 has the search for a directly referenced identifier climb until it
// finds an item of that name or meets a module, interface, program or checker
// boundary, and a generate block is not one of those boundaries, so a call
// written in a nested block names a function of the block enclosing it and a
// call written in any block names a function of the module. A name these items
// declare overwrites the entry they inherited, which is §23.9's identifier
// declared locally: its call names the block's function, which folds to
// nothing, rather than a module function of the same name.
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
    if (item->kind == ModuleItemKind::kFunctionDecl)
      decls[item->name] = nullptr;
  return true;
}

// Runs `elaborate`, which elaborates one item of the generate block instance
// `scope` into `mod`, and records what the item declared as members of that
// instance. Kept apart from ElaborateGenerateItems, which stands near the
// statement threshold.
template <typename Elaborate>
static void ElaborateRecordingMembers(RtlirModule* mod,
                                      const GenBlockInstanceScope& scope,
                                      const Elaborate& elaborate) {
  DeclarationCounts before = CountDeclarations(mod);
  elaborate();
  RecordBlockItemMembers(mod, scope, before);
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
  // §23.9 lists generate blocks among the elements that open a new scope, so
  // which of the module Elaborator::ProcessPendingGenerate registered the
  // folder may name from here depends on the blocks these items stand in. Every
  // caller sets ElaboratorData::gen_prefix_scopes_ to that before calling, so
  // this is the one site covering the conditional block, the directly nested
  // block that opens no scope of its own, and each iteration of a loop generate
  // block.
  RegisteredGenScopeGuard gen_scope_guard(gen_prefix_scopes_);
  // §26.3: an import these items write is a candidate for the items after it
  // alone, which Elaborator::ElaborateGenerateBlockImport records by adding a
  // step to gen_prefix_scopes_ as the walk reaches it. The steps are the
  // block's and end with its items, so the list is put back as it was found.
  GenBlockPrefixes entry_prefix_scopes = gen_prefix_scopes_;
  // §27.5 with §23.9, §6.18 and §3.13 (f): the enclosing scope's typedefs,
  // forward typedef kinds and typedef dimensions for the names these items
  // declare as typedefs or classes, out for the walk and back after it, the
  // block's own forward kinds and dimensions erased; see TakeEnclosingTypedefs.
  EnclosingTypedefs enclosing_typedefs = TakeEnclosingTypedefs(
      items, typedefs_, forward_typedef_kinds_, td_array_dims_);
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
  BlockDeclarationShadow block_declarations(&property_registry_, items);
  const std::vector<std::string_view> kDataNames = DeclaredDataNames(items);
  ShadowedEntries var_types(var_types_, kDataNames);
  ShadowedEntries class_var_types(class_var_types_, kDataNames);
  ShadowedEntries class_vars(class_var_names_, kDataNames);
  ShadowedEntries scalar_vars(scalar_var_names_, kDataNames);
  ShadowedEntries real_vars(real_var_names_, kDataNames);
  ShadowedEntries real_params(real_param_names_, kDataNames);
  ShadowedEntries select_shapes(var_select_shapes_, kDataNames);
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
        ElaborateRecordingMembers(
            mod, {gen_block_path_, gen_prefix_, gen_prefix_scopes_},
            [&] { ElaborateGenerateBlockItem(item, mod); });
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
                           forward_typedef_kinds_, td_array_dims_);
  gen_prefix_scopes_ = std::move(entry_prefix_scopes);
  mod->default_disable_iff = enclosing_default_disable_iff;
  gen_const_scope_ = saved_gen_const_scope;
}

// The queues and tables a design's elaboration fills, emptied before the next
// one starts: the generate constructs pending and the defparams applied,
// queued, rooted and written.
void Elaborator::ResetPendingElaboration() {
  pending_generates_.clear();
  applied_defparams_.clear();
  generate_defparams_.clear();
  defparam_top_roots_.clear();
  defparam_writer_blocks_.clear();
}

}  // namespace delta
