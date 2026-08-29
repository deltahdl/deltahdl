// The bodies of the tables src/simulator/sim_context_name_tables.h declares:
// the functions, let declarations and sequence declarations a module
// registers, the real, string and chandle variables, the unbounded
// parameters, the enumeration and structure types with the type each variable
// was declared of, the width recorded for a named type, the type of each
// module instance, the §26.3 imported names, the §23.4 nested declaration
// scopes and the §25.9 virtual interface bindings. Each records one entry or
// answers one lookup.
//
// ResolveStructFieldPath stands here too, with the structure types it reads.
// src/simulator/sim_context_types.h declares it and eval_expr.cpp,
// assoc_element.cpp and statement_assign.cpp call it to turn a dotted member
// path into the bit offset, width and type of the field it names.
//
// The rest of the context is in src/simulator/sim_context.h.

#include "simulator/sim_context_name_tables.h"

#include <string>
#include <string_view>

#include "simulator/sim_context_types.h"

namespace delta {

void DeclaredNameTables::RegisterFunction(std::string_view name,
                                          ModuleItem* item) {
  functions_[name] = item;
}

ModuleItem* DeclaredNameTables::FindFunction(std::string_view name) {
  auto it = functions_.find(name);
  return (it != functions_.end()) ? it->second : nullptr;
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

void DeclaredNameTables::RegisterRealVariable(std::string_view name) {
  real_vars_.insert(name);
}

bool DeclaredNameTables::IsRealVariable(std::string_view name) const {
  return real_vars_.count(name) != 0;
}

void DeclaredNameTables::RegisterImportedName(std::string_view name) {
  imported_names_.insert(name);
}

void DeclaredNameTables::RegisterNestedDeclScope(std::string_view prefix) {
  nested_decl_scopes_.insert(std::string(prefix));
}

void DeclaredNameTables::RegisterStringVariable(std::string_view name) {
  string_vars_.insert(name);
}

bool DeclaredNameTables::IsStringVariable(std::string_view name) const {
  return string_vars_.count(name) != 0;
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

static const StructFieldInfo* FindStructField(const StructTypeInfo* info,
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

void DeclaredNameTables::RegisterVirtualInterfaceVar(const Variable* v) {
  if (v) vi_vars_.insert(v);
}

bool DeclaredNameTables::IsVirtualInterfaceVar(const Variable* v) const {
  return v && vi_vars_.count(v) != 0;
}

void DeclaredNameTables::BindVirtualInterface(const Variable* v,
                                              std::string_view scope) {
  if (v) vi_bindings_[v] = std::string(scope);
}

void DeclaredNameTables::UnbindVirtualInterface(const Variable* v) {
  vi_bindings_.erase(v);
}

bool DeclaredNameTables::VirtualInterfaceIsBound(const Variable* v) const {
  return vi_bindings_.find(v) != vi_bindings_.end();
}

std::string_view DeclaredNameTables::VirtualInterfaceBinding(
    const Variable* v) const {
  auto it = vi_bindings_.find(v);
  return (it != vi_bindings_.end()) ? std::string_view(it->second)
                                    : std::string_view{};
}

}  // namespace delta
