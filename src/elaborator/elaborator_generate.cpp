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

void Elaborator::ProcessPendingGenerate(const PendingGenerate& pg) {
  TypedefMap saved_typedefs = std::move(typedefs_);
  ScopeMap saved_cu_param_scope = std::move(cu_param_scope_);
  auto saved_td_array_dims = std::move(td_array_dims_);
  typedefs_ = pg.typedefs;
  cu_param_scope_ = pg.cu_param_scope;
  td_array_dims_ = pg.td_array_dims;
  std::string saved_config_path =
      std::exchange(config_inst_path_, pg.config_inst_path);
  std::string saved_library = std::exchange(current_library_, pg.library);
  ModuleScopeNames enclosing = std::move(module_scope_names_[pg.mod]);
  SwapModuleScopeNames(enclosing);
  ParamRangeRegistryGuard param_range_guard(pg.mod);
  TypedefRegistryGuard typedef_guard(&typedefs_, &aggregate_typedef_names_,
                                     &type_ref_compare_);
  std::unordered_map<std::string_view, const ClassDecl*> param_class_registry =
      BuildParamClassRegistry(unit_);
  ParamClassRegistryGuard param_class_guard(&param_class_registry);
  ConstFuncRegistryGuard const_func_guard(&pg.func_decls);
  PropertyRegistry saved_property_registry = std::move(property_registry_);
  property_registry_ = pg.property_registry;
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
  ValidateGenerateValueParams(pg.item, pg.mod, scope, diag_);
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
  SwapModuleScopeNames(enclosing);
  module_scope_names_[pg.mod] = std::move(enclosing);
}

template <typename Item>
static void StampGenBlockInstance(std::vector<Item>& items, size_t first,
                                  const GenBlockConsts& consts,
                                  const GenBlockPrefixes& prefixes) {
  for (size_t i = first; i < items.size(); ++i) {
    items[i].gen_block_consts = consts;
    items[i].gen_block_prefixes = prefixes;
  }
}

template <typename Scoped>
static void StampGenBlockScope(std::vector<Scoped>& items, size_t first,
                               const HierPath& path,
                               const GenBlockPrefixes& prefixes) {
  for (size_t i = first; i < items.size(); ++i) {
    items[i].gen_block_path = path;
    items[i].gen_block_prefixes = prefixes;
  }
}

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
  bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                       item->kind == ModuleItemKind::kTaskDecl;
  if (is_subroutine && item->method_class.empty()) {
    mod->gen_block_subroutines.push_back(
        {item, gen_block_path_, gen_loop_consts_, gen_prefix_scopes_});
  }
  if (item->kind == ModuleItemKind::kTypedef) {
    mod->gen_block_typedefs.push_back({item, gen_block_path_});
  }
  StampGenBlockInstance(mod->processes, first_proc, gen_loop_consts_,
                        gen_prefix_scopes_);
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
  StampGenBlockInstance(mod->children, first_child, gen_loop_consts_,
                        gen_prefix_scopes_);
  for (size_t i = first_alias; i < mod->aliases.size(); ++i) {
    mod->aliases[i].gen_block_prefixes = gen_prefix_scopes_;
  }
}

struct EnclosingTypedefs {
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
  ScopeMap saved_gen_const_scope = gen_const_scope_;
  gen_const_scope_ = scope;
  RegisteredGenScopeGuard gen_scope_guard(gen_prefix_scopes_);
  GenBlockPrefixes entry_prefix_scopes = gen_prefix_scopes_;
  EnclosingTypedefs enclosing_typedefs = TakeEnclosingTypedefs(
      items, typedefs_, forward_typedef_kinds_, td_array_dims_);
  std::unordered_map<std::string_view, const ModuleItem*> gen_func_decls;
  std::optional<ConstFuncRegistryGuard> gen_func_guard;
  if (CollectGenerateBlockFunctions(items, gen_func_decls)) {
    gen_func_guard.emplace(&gen_func_decls);
  }
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
  ResolveModuleSubroutineFormalTypes(items, typedefs_, arena_);
  RestoreEnclosingTypedefs(enclosing_typedefs, typedefs_,
                           forward_typedef_kinds_, td_array_dims_);
  gen_prefix_scopes_ = std::move(entry_prefix_scopes);
  mod->default_disable_iff = enclosing_default_disable_iff;
  gen_const_scope_ = saved_gen_const_scope;
}

void Elaborator::ResetPendingElaboration() {
  pending_generates_.clear();
  applied_defparams_.clear();
  generate_defparams_.clear();
  defparam_top_roots_.clear();
  defparam_writer_blocks_.clear();
}

}  // namespace delta
