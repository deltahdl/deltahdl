// The bodies of the tables src/simulator/sim_context_name_tables.h declares:
// the functions, let declarations and sequence declarations a module
// registers, the real, string and chandle variables, the unbounded
// parameters, the enumeration and structure types with the type each variable
// was declared of, the width recorded for a named type, the type of each
// module instance, the §26.3 imported names, the §23.4 nested declaration
// scopes and the §25.9 virtual interface handles. Each records one entry or
// answers one lookup.
//
// ResolveStructFieldPath stands here too, with the structure types it reads.
// src/simulator/sim_context_types.h declares it and eval_expr.cpp,
// assoc_element.cpp and statement_assign.cpp call it to turn a dotted member
// path into the bit offset, width and type of the field it names.
//
// The rest of the context is in src/simulator/sim_context.h.

#include "simulator/sim_context_name_tables.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

void DeclaredNameTables::RegisterFunction(std::string_view name,
                                          ModuleItem* item) {
  functions_[name] = item;
}

ModuleItem* DeclaredNameTables::FindFunction(std::string_view name) {
  auto it = functions_.find(name);
  return (it != functions_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterGenBlockSubroutineScope(
    std::string_view key, GenBlockSubroutineScope scope) {
  gen_block_subroutine_scopes_[key] = std::move(scope);
}

const GenBlockSubroutineScope* DeclaredNameTables::FindGenBlockSubroutineScope(
    std::string_view key) const {
  auto it = gen_block_subroutine_scopes_.find(key);
  return (it != gen_block_subroutine_scopes_.end()) ? &it->second : nullptr;
}

void DeclaredNameTables::RegisterLetDecl(std::string_view name,
                                         ModuleItem* item) {
  let_decls_[name] = item;
}

ModuleItem* DeclaredNameTables::FindLetDecl(std::string_view name) {
  auto it = let_decls_.find(name);
  return (it != let_decls_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterSequenceDecl(std::string_view name,
                                              ModuleItem* item) {
  sequence_decls_[name] = item;
}

ModuleItem* DeclaredNameTables::FindSequenceDecl(std::string_view name) {
  auto it = sequence_decls_.find(name);
  return (it != sequence_decls_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterPropertyDecl(std::string_view name,
                                              ModuleItem* item) {
  property_decls_[name] = item;
}

ModuleItem* DeclaredNameTables::FindPropertyDecl(std::string_view name) {
  auto it = property_decls_.find(name);
  return (it != property_decls_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterSequenceInstanceEndpoint(
    const Expr* instance, std::string_view ep_name) {
  sequence_instance_eps_[instance] = ep_name;
}

std::string_view DeclaredNameTables::FindSequenceInstanceEndpoint(
    const Expr* instance) const {
  auto it = sequence_instance_eps_.find(instance);
  return (it != sequence_instance_eps_.end()) ? it->second : std::string_view{};
}

bool DeclaredNameTables::ConsumeSequenceMatch(std::string_view ep_name,
                                              uint64_t matched_ticks,
                                              uint64_t now) {
  if (matched_ticks == UINT64_MAX || matched_ticks > now) return false;
  auto it = sequence_match_reads_.find(ep_name);
  if (it != sequence_match_reads_.end() && it->second >= matched_ticks &&
      it->second != now) {
    return false;
  }
  sequence_match_reads_[ep_name] = now;
  return true;
}

void DeclaredNameTables::RegisterRealVariable(std::string_view name) {
  real_vars_.insert(name);
}

bool DeclaredNameTables::IsRealVariable(std::string_view name) const {
  return real_vars_.count(name) != 0;
}

void DeclaredNameTables::RegisterImportedName(std::string_view name) {
  imported_names_.insert(name);
}

bool DeclaredNameTables::IsImportedName(std::string_view name) const {
  if (imported_names_.count(name) != 0) return true;
  size_t bracket = name.find('[');
  return bracket != std::string_view::npos &&
         imported_names_.count(name.substr(0, bracket)) != 0;
}

void DeclaredNameTables::RegisterSubroutinePackage(const ModuleItem* subroutine,
                                                   std::string_view pkg) {
  subroutine_packages_[subroutine] = pkg;
}

std::string_view DeclaredNameTables::SubroutinePackage(
    const ModuleItem* subroutine) const {
  auto it = subroutine_packages_.find(subroutine);
  return it != subroutine_packages_.end() ? it->second : std::string_view{};
}

void DeclaredNameTables::RegisterPackageImport(std::string_view pkg,
                                               std::string_view imported,
                                               std::string_view item) {
  package_imports_[pkg].push_back({imported, item});
}

std::vector<std::string> DeclaredNameTables::PackageScopedKeys(
    std::string_view pkg, std::string_view name) const {
  std::vector<std::string> keys;
  keys.push_back(std::string(pkg) + "." + std::string(name));
  auto it = package_imports_.find(pkg);
  if (it == package_imports_.end()) return keys;
  for (const PackageImport& imp : it->second) {
    if (imp.item != "*" && imp.item != name) continue;
    keys.push_back(std::string(imp.imported) + "." + std::string(name));
  }
  return keys;
}

std::vector<std::string> GenerateBlockKeys(
    std::string_view inst_prefix, const std::vector<std::string>& gen_prefixes,
    std::string_view name) {
  std::vector<std::string> keys;
  keys.reserve(gen_prefixes.size());
  for (auto it = gen_prefixes.rbegin(); it != gen_prefixes.rend(); ++it) {
    keys.push_back(std::string(inst_prefix) + *it + std::string(name));
  }
  return keys;
}

void DeclaredNameTables::RegisterNestedDeclScope(std::string_view prefix) {
  nested_decl_scopes_.insert(std::string(prefix));
}

void DeclaredNameTables::RegisterChandleVariable(std::string_view name) {
  chandle_vars_.insert(name);
}

bool DeclaredNameTables::IsChandleVariable(std::string_view name) const {
  return chandle_vars_.count(name) != 0;
}

void DeclaredNameTables::RegisterUnboundedParam(std::string_view name) {
  unbounded_params_.insert(name);
}

bool DeclaredNameTables::IsUnboundedParam(std::string_view name) const {
  return unbounded_params_.count(name) != 0;
}

void DeclaredNameTables::RegisterEnumType(std::string_view name,
                                          const EnumTypeInfo& info) {
  enum_types_[name] = info;
}

const EnumTypeInfo* DeclaredNameTables::FindEnumType(
    std::string_view name) const {
  auto it = enum_types_.find(name);
  return (it != enum_types_.end()) ? &it->second : nullptr;
}

void DeclaredNameTables::SetVariableEnumType(std::string_view var_name,
                                             std::string_view type_name) {
  var_enum_types_[var_name] = type_name;
}

const EnumTypeInfo* DeclaredNameTables::GetVariableEnumType(
    std::string_view var_name) const {
  auto it = var_enum_types_.find(var_name);
  if (it == var_enum_types_.end()) return nullptr;
  return FindEnumType(it->second);
}

static bool DeclaresMember(const EnumTypeInfo& info, std::string_view member) {
  for (const EnumMemberInfo& m : info.members) {
    if (m.name == member) return true;
  }
  return false;
}

const EnumTypeInfo* DeclaredNameTables::FindEnumTypeDeclaringMember(
    std::string_view member, std::string_view scope) const {
  const EnumTypeInfo* scoped = nullptr;
  for (const auto& [key, info] : enum_types_) {
    if (!DeclaresMember(info, member)) continue;
    auto sep = key.find("::");
    if (!scope.empty()) {
      if (sep != std::string_view::npos && key.substr(0, sep) == scope)
        return &info;
      continue;
    }
    if (sep == std::string_view::npos) return &info;
    if (scoped == nullptr) scoped = &info;
  }
  return scoped;
}

const StructFieldInfo* FindStructField(const StructTypeInfo* info,
                                       std::string_view name) {
  for (const auto& f : info->fields) {
    if (f.name == name) return &f;
  }
  return nullptr;
}

bool ResolveStructFieldPath(const StructTypeInfo* info, std::string_view path,
                            uint32_t* bit_offset, uint32_t* width,
                            DataTypeKind* out_kind) {
  uint32_t acc = 0;
  while (info) {
    auto dot = path.find('.');
    auto seg = dot == std::string_view::npos ? path : path.substr(0, dot);
    const StructFieldInfo* f = FindStructField(info, seg);
    if (!f) return false;
    acc += f->bit_offset;
    if (dot == std::string_view::npos) {
      *bit_offset = acc;
      *width = f->width;
      if (out_kind) *out_kind = f->type_kind;
      return true;
    }
    info = f->nested;
    path = path.substr(dot + 1);
  }
  return false;
}

void DeclaredNameTables::RegisterStructType(std::string_view name,
                                            const StructTypeInfo& info) {
  struct_types_[name] = info;
}

const StructTypeInfo* DeclaredNameTables::FindStructType(
    std::string_view name) const {
  auto it = struct_types_.find(name);
  return (it != struct_types_.end()) ? &it->second : nullptr;
}

void DeclaredNameTables::SetVariableStructType(std::string_view var_name,
                                               std::string_view type_name) {
  var_struct_types_[var_name] = type_name;
}

const StructTypeInfo* DeclaredNameTables::GetVariableStructType(
    std::string_view var_name) const {
  auto it = var_struct_types_.find(var_name);
  if (it == var_struct_types_.end()) return nullptr;
  return FindStructType(it->second);
}

void DeclaredNameTables::RegisterTypeWidth(std::string_view name,
                                           uint32_t width) {
  type_widths_[name] = width;
}

uint32_t DeclaredNameTables::FindTypeWidth(std::string_view name) const {
  auto it = type_widths_.find(name);
  return (it != type_widths_.end()) ? it->second : 0;
}

void DeclaredNameTables::RegisterVariableClassTypeParams(
    std::string_view var, const std::vector<DataType>* params) {
  var_class_type_params_[var] = params;
}

const std::vector<DataType>* DeclaredNameTables::FindVariableClassTypeParams(
    std::string_view var) const {
  auto it = var_class_type_params_.find(var);
  return (it != var_class_type_params_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterTypeKind(std::string_view name,
                                          DataTypeKind kind) {
  type_kinds_[name] = kind;
}

DataTypeKind DeclaredNameTables::FindTypeKind(std::string_view name) const {
  auto it = type_kinds_.find(name);
  return (it != type_kinds_.end()) ? it->second : DataTypeKind::kNamed;
}

void DeclaredNameTables::RegisterTypeSigned(std::string_view name,
                                            bool is_signed) {
  type_signed_[name] = is_signed;
}

bool DeclaredNameTables::FindTypeSigned(std::string_view name) const {
  auto it = type_signed_.find(name);
  return it != type_signed_.end() && it->second;
}

void DeclaredNameTables::RegisterTypeRange(std::string_view name,
                                           PackedRange range) {
  type_ranges_[name] = range;
}

std::optional<PackedRange> DeclaredNameTables::FindTypeRange(
    std::string_view name) const {
  auto it = type_ranges_.find(name);
  if (it == type_ranges_.end()) return std::nullopt;
  return it->second;
}

void DeclaredNameTables::RegisterTypeTarget(std::string_view name,
                                            std::string_view target) {
  type_targets_[name] = target;
}

std::string_view DeclaredNameTables::FindTypeTarget(
    std::string_view name) const {
  auto it = type_targets_.find(name);
  return (it != type_targets_.end()) ? it->second : std::string_view{};
}

size_t DeclaredNameTables::TypeTargetCount() const {
  return type_targets_.size();
}

void DeclaredNameTables::RegisterTypeDeclaration(std::string_view name,
                                                 const ModuleItem* item) {
  type_declarations_[name] = item;
}

const DataType* DeclaredNameTables::FindTypeDeclaration(
    std::string_view name) const {
  const ModuleItem* item = FindTypedefItem(name);
  return item != nullptr ? &item->typedef_type : nullptr;
}

const ModuleItem* DeclaredNameTables::FindTypedefItem(
    std::string_view name) const {
  auto it = type_declarations_.find(name);
  return (it != type_declarations_.end()) ? it->second : nullptr;
}

size_t DeclaredNameTables::TypeDeclarationCount() const {
  return type_declarations_.size();
}

void DeclaredNameTables::BindSemaphoreHandle(const Variable* var,
                                             SemaphoreObject* sem) {
  semaphore_handles_[var] = sem;
}

SemaphoreObject* DeclaredNameTables::SemaphoreOfHandle(
    const Variable* var) const {
  auto it = semaphore_handles_.find(var);
  return (it != semaphore_handles_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::BindMailboxHandle(const Variable* var,
                                           MailboxObject* mbx) {
  mailbox_handles_[var] = mbx;
}

MailboxObject* DeclaredNameTables::MailboxOfHandle(const Variable* var) const {
  auto it = mailbox_handles_.find(var);
  return (it != mailbox_handles_.end()) ? it->second : nullptr;
}

void DeclaredNameTables::RegisterInstanceType(std::string_view prefix,
                                              std::string_view type) {
  instance_types_[std::string(prefix)] = std::string(type);
}

std::string_view DeclaredNameTables::FindInstanceType(
    std::string_view prefix) const {
  auto it = instance_types_.find(std::string(prefix));
  return (it != instance_types_.end()) ? std::string_view(it->second)
                                       : std::string_view{};
}

void DeclaredNameTables::RegisterTopModule(std::string_view name) {
  top_module_names_.insert(std::string(name));
}

bool DeclaredNameTables::IsTopModule(std::string_view name) const {
  return top_module_names_.count(std::string(name)) != 0;
}

uint64_t DeclaredNameTables::VirtualInterfaceHandle(std::string_view scope) {
  auto it = vi_instance_handles_.find(std::string(scope));
  if (it != vi_instance_handles_.end()) return it->second;
  vi_instance_scopes_.emplace_back(scope);
  uint64_t handle = vi_instance_scopes_.size();
  vi_instance_handles_[std::string(scope)] = handle;
  return handle;
}

std::string_view DeclaredNameTables::VirtualInterfaceScope(
    uint64_t handle) const {
  if (handle == 0 || handle > vi_instance_scopes_.size()) return {};
  return vi_instance_scopes_[handle - 1];
}

void DeclaredNameTables::RegisterVirtualInterfaceVar(Variable* v) {
  if (v) v->is_virtual_interface = true;
}

bool DeclaredNameTables::IsVirtualInterfaceVar(const Variable* v) const {
  return v && v->is_virtual_interface;
}

bool DeclaredNameTables::VirtualInterfaceIsBound(const Variable* v) const {
  return !VirtualInterfaceBinding(v).empty();
}

std::string_view DeclaredNameTables::VirtualInterfaceBinding(
    const Variable* v) const {
  if (!IsVirtualInterfaceVar(v)) return {};
  return VirtualInterfaceScope(v->value.ToUint64());
}

}  // namespace delta
