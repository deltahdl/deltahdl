#pragma once

// The tables SimContext keys by a declared name and answers from while the
// design runs: the functions, let declarations and sequence declarations a
// module registers; the real, string and chandle variables and the unbounded
// parameters; the enumeration and structure types, together with the type each
// variable was declared of; the width recorded for a named type; the type of
// each module instance; the names a package import makes visible (§26.3) and
// the scopes a nested module declaration opens (§23.4); and the §25.9 virtual
// interface handles. Every declaration keeps the comment it carried in
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
#include <vector>

#include "parser/ast_type.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

class DeclaredNameTables {
 public:
  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  // §27.4 with §13.4 and §23.6: the scope the subroutine registered under
  // `key` runs in, recorded for a subroutine a generate block instance
  // declares, under the instance-qualified key a hierarchical call resolves
  // by, "blk[1].triple"; FindGenBlockSubroutineScope answers null for a key
  // no generate block's subroutine is registered under. `key` must outlive
  // the context.
  void RegisterGenBlockSubroutineScope(std::string_view key,
                                       GenBlockSubroutineScope scope);
  const GenBlockSubroutineScope* FindGenBlockSubroutineScope(
      std::string_view key) const;

  void RegisterLetDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindLetDecl(std::string_view name);

  void RegisterSequenceDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindSequenceDecl(std::string_view name);
  // §16.12: a named property declaration, which an instance in a property
  // tree is expanded from when it begins.
  void RegisterPropertyDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindPropertyDecl(std::string_view name);

  // §16.9.11: `e2(ready, proc1, proc2).triggered` applies the method to an
  // instance with arguments, which is matched by a monitor of its own; the
  // lowering registers the endpoint event that monitor fires under the
  // instance as written, and the evaluator reads it back by the same
  // expression. `ep_name` must outlive the context.
  void RegisterSequenceInstanceEndpoint(const Expr* instance,
                                        std::string_view ep_name);
  std::string_view FindSequenceInstanceEndpoint(const Expr* instance) const;

  // §16.13.5: `matched` on a sequence stores the result of a match of it
  // until the first tick of the reading sequence's clock after the match:
  // whether the end point named `ep_name`, last reached at `matched_ticks`
  // (kNever for never), is matched as read at `now`, a read at a time step
  // consuming the match for the time steps after it. `ep_name` must outlive
  // the context.
  bool ConsumeSequenceMatch(std::string_view ep_name, uint64_t matched_ticks,
                            uint64_t now);

  void RegisterRealVariable(std::string_view name);
  bool IsRealVariable(std::string_view name) const;

  // §26.3: a name a package import makes visible belongs to no module, so
  // FindVariable answers it from inside an instance where §23.9 stops an
  // enclosing module's variable. `name` must outlive the context.
  void RegisterImportedName(std::string_view name);

  // §26.3 with §13.4: the package a subroutine was declared in, whose
  // variables its body reads by their bare names, and the package's own
  // imports, through which it reads another package's. `pkg` and the import's
  // names must outlive the context; `item` is "*" for a wildcard import.
  void RegisterSubroutinePackage(const ModuleItem* subroutine,
                                 std::string_view pkg);
  std::string_view SubroutinePackage(const ModuleItem* subroutine) const;
  void RegisterPackageImport(std::string_view pkg, std::string_view imported,
                             std::string_view item);
  // The keys a bare `name` read in package `pkg` may stand under, in the
  // order §26.3 resolves them: the package's own declaration, then each
  // package an import of `pkg` brings the name in from.
  std::vector<std::string> PackageScopedKeys(std::string_view pkg,
                                             std::string_view name) const;

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

  // §6.18: the kind the type a name stands for resolves to, which the width
  // cannot say -- EvalTypeWidth answers 0 for a string, an event, a class
  // handle and a type it could not size alike. DataTypeKind::kNamed is the
  // answer for a name the elaborated table does not hold, which is what a name
  // standing for nothing this run knows about answers too.
  void RegisterTypeKind(std::string_view name, DataTypeKind kind);
  DataTypeKind FindTypeKind(std::string_view name) const;

  // §6.11.1: whether the type a name stands for is signed, which neither the
  // width nor the kind can say -- `logic signed [7:0]` and `logic [7:0]` are
  // one kind at one width. False for a name the elaborated table does not hold,
  // which is what an unsigned type answers too.
  void RegisterTypeSigned(std::string_view name, bool is_signed);
  bool FindTypeSigned(std::string_view name) const;

  void RegisterInstanceType(std::string_view prefix, std::string_view type);
  std::string_view FindInstanceType(std::string_view prefix) const;

  // §23.6: each top-level module is the root of a name hierarchy, and the
  // complete path to any object starts at one of them, usable from a parallel
  // hierarchy -- `m.a` written in the other top-level module n. A top's own
  // declarations are keyed under no instance prefix, so a lookup that meets
  // one of these names at the head of a path drops it and reads the rest.
  void RegisterTopModule(std::string_view name);
  bool IsTopModule(std::string_view name) const;

  // §8.25: the parameter actuals the declaration of the class variable `var`
  // wrote in its `#(...)`, as the parser recorded them, one DataType per
  // actual in the order written (or with param_arg_name set for the named
  // form). A type actual has no expression for
  // SimContext::GetVariableClassParamExprs to carry -- `string` is a type, not
  // a value -- so this is what binds a type parameter to the object a `new` on
  // the variable constructs (ApplyClassParamOverrides in
  // src/simulator/eval_function.cpp). The list lives in the declaration's AST,
  // which outlives the run. Null for a variable declared with no `#(...)`.
  void RegisterVariableClassTypeParams(std::string_view var,
                                       const std::vector<DataType>* params);
  const std::vector<DataType>* FindVariableClassTypeParams(
      std::string_view var) const;

  // §25.9 virtual interface runtime. A virtual interface is a value: the
  // handle of the interface instance it represents, held in the 64-bit
  // Logic4Vec of whatever declares it -- a module variable, a subroutine
  // formal, a class property, an element of a container -- as a class handle
  // is held, so that an assignment, an argument, a property write and a copy
  // of an object carry it with no table to keep in step. The handle is the
  // 1-based position of the instance's scope in vi_instance_scopes_, issued
  // the first time the instance is asked for; 0 is the null of §25.9, which
  // is also what every declaration holds before it is initialized.
  uint64_t VirtualInterfaceHandle(std::string_view scope);
  // The scope of the instance `handle` denotes; empty for 0 and for a number
  // no instance was issued.
  std::string_view VirtualInterfaceScope(uint64_t handle) const;

  // The three questions asked of a variable declared `virtual interface` --
  // whether it is one, whether it holds an instance, and which -- answered
  // from Variable::is_virtual_interface and the value it holds.
  void RegisterVirtualInterfaceVar(Variable* v);
  bool IsVirtualInterfaceVar(const Variable* v) const;
  bool VirtualInterfaceIsBound(const Variable* v) const;
  std::string_view VirtualInterfaceBinding(const Variable* v) const;

 protected:
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  // §27.4 with §13.4: see RegisterGenBlockSubroutineScope.
  std::unordered_map<std::string_view, GenBlockSubroutineScope>
      gen_block_subroutine_scopes_;
  std::unordered_map<std::string_view, ModuleItem*> let_decls_;
  std::unordered_map<std::string_view, ModuleItem*> sequence_decls_;
  std::unordered_map<std::string_view, ModuleItem*> property_decls_;
  std::unordered_map<const Expr*, std::string_view> sequence_instance_eps_;
  // §16.13.5: the time step each end point's match was last read as matched.
  std::unordered_map<std::string_view, uint64_t> sequence_match_reads_;

  std::unordered_set<std::string_view> real_vars_;

  // §26.3: see RegisterImportedName.
  std::unordered_set<std::string_view> imported_names_;
  // §26.3 with §13.4: see RegisterSubroutinePackage.
  std::unordered_map<const ModuleItem*, std::string_view> subroutine_packages_;
  struct PackageImport {
    std::string_view imported;
    std::string_view item;
  };
  std::unordered_map<std::string_view, std::vector<PackageImport>>
      package_imports_;
  // §23.4: see RegisterNestedDeclScope.
  std::unordered_set<std::string> nested_decl_scopes_;

  std::unordered_set<std::string_view> chandle_vars_;

  std::unordered_set<std::string_view> unbounded_params_;

  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;

  std::unordered_map<std::string_view, StructTypeInfo> struct_types_;
  std::unordered_map<std::string_view, std::string_view> var_struct_types_;

  std::unordered_map<std::string_view, uint32_t> type_widths_;
  std::unordered_map<std::string_view, DataTypeKind> type_kinds_;
  std::unordered_map<std::string_view, bool> type_signed_;

  std::unordered_map<std::string, std::string> instance_types_;
  std::unordered_set<std::string> top_module_names_;
  std::unordered_map<std::string_view, const std::vector<DataType>*>
      var_class_type_params_;

  // §25.9: the scope of each interface instance a virtual interface handle
  // has been issued for, at handle minus one, and the handle each scope was
  // issued.
  std::vector<std::string> vi_instance_scopes_;
  std::unordered_map<std::string, uint64_t> vi_instance_handles_;
};

}  // namespace delta
