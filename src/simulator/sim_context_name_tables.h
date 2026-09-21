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

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/packed_range.h"
#include "parser/ast_type.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

struct MailboxObject;
struct SemaphoreObject;

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
  // Whether `name` is one so registered, or an element of one: §7.4.2 makes
  // the elements of an imported array, keyed `a[1]` under the import's key
  // (AliasArray in lowerer_import.cpp), the imported declaration's own, so
  // the key up to its first bracket is the one asked for.
  bool IsImportedName(std::string_view name) const;

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
  // §6.19: a member literal is an expression of the enumeration that declares
  // it, so the methods of §6.19.5 are called on it, `IDLE.next()` or
  // `P::RED.name()`. The registered enumeration whose members hold `member`:
  // one registered under `scope` ("P" for a package's, a class's name for a
  // class's) when `scope` is given, else one of the module's own -- a bare
  // key, where an import's is entered too -- ahead of any scoped one, since a
  // bare literal names what is visible where it is written. Null where none
  // declares the member.
  const EnumTypeInfo* FindEnumTypeDeclaringMember(std::string_view member,
                                                  std::string_view scope) const;

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

  // §11.5.1: the packed range the type a name stands for was declared with,
  // which the width cannot say -- `bit [15:10]` and `bit [5:0]` are one width
  // and the same index addresses a different bit of each. Recorded for the
  // names the elaborated table gives one, RtlirDesign::type_ranges, and empty
  // for every other name, whose variables are addressed as [width-1:0].
  void RegisterTypeRange(std::string_view name, PackedRange range);
  std::optional<PackedRange> FindTypeRange(std::string_view name) const;

  // §6.18: the name at the end of the chain of typedefs `name` stands for,
  // as the elaborated table records it (RtlirDesign::type_targets) for every
  // name whose chain ends in a name the typedef table does not resolve -- a
  // class, the built-in semaphore and mailbox among them -- under the
  // "pkg::name" key of a package's typedef (§26.3) and the bare key of a
  // module's, the unit's or an import's. Empty for a name nothing records.
  // TypeTargetCount bounds a walk of the chain, so a name recorded as
  // standing for itself cannot spin it. Filled by RegisterClassTypeAliases in
  // lowerer_register.cpp; before it the run held no table of what a typedef
  // stands for, so a property declared `mb_t mb` through `typedef mailbox
  // #(int) mb_t` was of no type the run knew.
  void RegisterTypeTarget(std::string_view name, std::string_view target);
  std::string_view FindTypeTarget(std::string_view name) const;
  size_t TypeTargetCount() const;

  // §6.18 with §15.4.9 (printed page 377 of ~/IEEE 1800-2023.pdf): the type the
  // typedef `name` was declared with, as the parser read it -- `mailbox #(int)`
  // with its parameter list, or another typedef's name, one step of the chain
  // -- keyed as the type targets are, "pkg::name" for a package's typedef and
  // the bare name for a module's or the unit's, and filled beside them by
  // RegisterClassTypeAliases from the design's typedef items. The targets
  // record the name at the end of the chain alone, so a property declared
  // `mb_t mb` through `typedef mailbox #(int) mb_t` was known for a mailbox
  // and not for one of int, and its put() of a string went unchecked. Null
  // for a name nothing records; TypeDeclarationCount bounds a walk of the
  // chain.
  void RegisterTypeDeclaration(std::string_view name, const DataType* type);
  const DataType* FindTypeDeclaration(std::string_view name) const;
  size_t TypeDeclarationCount() const;

  // §15.3 and §15.4 with §13.5.1: the semaphore or the mailbox the variable
  // `var` holds a handle to -- a subroutine formal declared `semaphore s` or
  // `mailbox m`, bound when the actual's object is copied in (BindSyncFormal
  // in eval_class_sync.cpp). The run keys a module's, an instance's and a
  // package's object by name, and a formal is a variable of the frame,
  // created per call in the arena (SimContext::CreateLocalVariable), so its
  // address is what it is known by and a later call's cell binds anew. Null
  // for a variable nothing bound.
  void BindSemaphoreHandle(const Variable* var, SemaphoreObject* sem);
  SemaphoreObject* SemaphoreOfHandle(const Variable* var) const;
  void BindMailboxHandle(const Variable* var, MailboxObject* mbx);
  MailboxObject* MailboxOfHandle(const Variable* var) const;

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
  // src/simulator/eval_class_params.cpp). The list lives in the declaration's
  // AST, which outlives the run. Null for a variable declared with no
  // `#(...)`.
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
  std::unordered_map<std::string_view, PackedRange> type_ranges_;

  // §6.18: see RegisterTypeTarget.
  std::unordered_map<std::string_view, std::string_view> type_targets_;
  // §6.18 with §15.4.9: see RegisterTypeDeclaration.
  std::unordered_map<std::string_view, const DataType*> type_declarations_;
  // §15.3 and §15.4 with §13.5.1: see BindSemaphoreHandle.
  std::unordered_map<const Variable*, SemaphoreObject*> semaphore_handles_;
  std::unordered_map<const Variable*, MailboxObject*> mailbox_handles_;

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

// §27.3 with §23.9 and §26.3: the keys a bare `name` may stand under in the
// generate block instances a process is in, innermost first -- the block's
// own declarations and the names an import written in it brings in, keyed
// under the instance's prefix and the block's, "blk.a" for a declaration of
// top's block `blk` and "blk.:import1:a" for its first import's
// (RtlirImport::scope_prefix, which Lowerer::AliasImportedPackageName keys
// by). `gen_prefixes` is the process's Process::gen_prefixes, outermost
// first, so the keys come out in the reverse order. SimContext::FindVariable
// reads a variable by them (FindInGenerateBlock) ahead of the instance's own
// key, and the object lookups take them in the same place.
std::vector<std::string> GenerateBlockKeys(
    std::string_view inst_prefix, const std::vector<std::string>& gen_prefixes,
    std::string_view name);

}  // namespace delta
