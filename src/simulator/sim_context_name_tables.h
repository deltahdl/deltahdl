#pragma once

// The tables SimContext keys by a declared name and answers from while the
// design runs: the functions, let declarations and sequence declarations a
// module registers; the real, string and chandle variables and the unbounded
// parameters; the enumeration and structure types, together with the type each
// variable was declared of; the width recorded for a named type; the type of
// each module instance; the names a package import makes visible (§26.3) and
// the scopes a nested module declaration opens (§23.4); and the §25.9 virtual
// interface bindings. Every declaration keeps the comment it carried in
// src/simulator/sim_context.h.
//
// Each body here records one entry or answers one lookup, reading no running
// process, no scope stack and no arena. The bodies that do read those stay
// with the rest of the context in src/simulator/sim_context.h and still reach
// these tables, which is why the members are protected rather than private:
// SimContext::FindVariable consults the §26.3 and §23.4 sets as it walks
// instance prefixes, and SimContext::ResolveInstanceScope walks the instance
// type table outwards from the instance the running process stands in.

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "simulator/sim_context_types.h"

namespace delta {

class DeclaredNameTables {
 public:
  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void RegisterLetDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindLetDecl(std::string_view name);

  void RegisterSequenceDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindSequenceDecl(std::string_view name);

  void RegisterRealVariable(std::string_view name);
  bool IsRealVariable(std::string_view name) const;

  // §26.3: a name a package import makes visible belongs to no module, so
  // FindVariable answers it from inside an instance where §23.9 stops an
  // enclosing module's variable. `name` must outlive the context.
  void RegisterImportedName(std::string_view name);

  // §23.4: records that the instance at `prefix` was declared inside the
  // module holding it, whose outer name space is visible to it.
  void RegisterNestedDeclScope(std::string_view prefix);

  // §21.2.1.6: chandle variables are tracked by name so the assignment-pattern
  // renderer can print a null (zero) handle as the word "null".
  void RegisterChandleVariable(std::string_view name);
  bool IsChandleVariable(std::string_view name) const;

  void RegisterUnboundedParam(std::string_view name);
  bool IsUnboundedParam(std::string_view name) const;

  void RegisterEnumType(std::string_view name, const EnumTypeInfo& info);
  const EnumTypeInfo* FindEnumType(std::string_view name) const;
  void SetVariableEnumType(std::string_view var_name,
                           std::string_view type_name);
  const EnumTypeInfo* GetVariableEnumType(std::string_view var_name) const;

  void RegisterStructType(std::string_view name, const StructTypeInfo& info);
  const StructTypeInfo* FindStructType(std::string_view name) const;
  void SetVariableStructType(std::string_view var_name,
                             std::string_view type_name);
  const StructTypeInfo* GetVariableStructType(std::string_view var_name) const;

  void RegisterTypeWidth(std::string_view name, uint32_t width);
  uint32_t FindTypeWidth(std::string_view name) const;

  void RegisterInstanceType(std::string_view prefix, std::string_view type);
  std::string_view FindInstanceType(std::string_view prefix) const;

  // §25.9 virtual interface runtime. A virtual interface variable carries a
  // binding to the scope of the interface instance it currently refers to, or
  // is unbound (the null state, which is also the value before initialization).
  // Bindings are keyed by the variable object, so no name re-resolution is
  // needed when the binding is later consulted.
  void RegisterVirtualInterfaceVar(const Variable* v);
  bool IsVirtualInterfaceVar(const Variable* v) const;
  void BindVirtualInterface(const Variable* v, std::string_view scope);
  void UnbindVirtualInterface(const Variable* v);
  bool VirtualInterfaceIsBound(const Variable* v) const;
  std::string_view VirtualInterfaceBinding(const Variable* v) const;

 protected:
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::unordered_map<std::string_view, ModuleItem*> let_decls_;
  std::unordered_map<std::string_view, ModuleItem*> sequence_decls_;

  std::unordered_set<std::string_view> real_vars_;

  // §26.3: see RegisterImportedName.
  std::unordered_set<std::string_view> imported_names_;
  // §23.4: see RegisterNestedDeclScope.
  std::unordered_set<std::string> nested_decl_scopes_;

  std::unordered_set<std::string_view> chandle_vars_;

  std::unordered_set<std::string_view> unbounded_params_;

  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;

  std::unordered_map<std::string_view, StructTypeInfo> struct_types_;
  std::unordered_map<std::string_view, std::string_view> var_struct_types_;

  std::unordered_map<std::string_view, uint32_t> type_widths_;

  std::unordered_map<std::string, std::string> instance_types_;

  // §25.9: virtual interface variables and their current interface-instance
  // scope bindings (absence of a binding means null / uninitialized).
  std::unordered_set<const Variable*> vi_vars_;
  std::unordered_map<const Variable*, std::string> vi_bindings_;
};

}  // namespace delta
