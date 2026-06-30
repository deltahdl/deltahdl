#pragma once

#include <cstdint>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

struct ClassDecl;
struct ClassMember;
struct Expr;
struct ModuleItem;
class Arena;

enum class Reachability : std::uint8_t {
  kStronglyReachable,
  kWeaklyReachable,
  kUnreachable,
};

struct ClassTypeInfo;
struct ClassTypespecInfo;

struct VTableEntry {
  std::string_view method_name;
  ModuleItem* method = nullptr;
  const ClassTypeInfo* owner = nullptr;
};

struct ClassTypeInfo {
  std::string_view name;
  const ClassTypeInfo* parent = nullptr;
  const ClassDecl* decl = nullptr;
  bool is_abstract = false;
  bool is_interface = false;
  // §37.32: a built-in class has no user-written declaration; its class-defn
  // relation reports NULL.
  bool is_builtin = false;
  std::vector<const ClassTypeInfo*> extended_interfaces;

  struct PropertyInfo {
    std::string_view name;
    uint32_t width = 32;
    bool is_static = false;
    bool is_local = false;
    bool is_protected = false;
    bool is_const = false;
    Expr* init_expr = nullptr;
  };
  std::vector<PropertyInfo> properties;

  std::unordered_map<std::string, ModuleItem*> methods;

  std::vector<VTableEntry> vtable;

  // §8.9: static class properties are shared state that changes at run time,
  // even though the type descriptor itself is referenced as const. mutable lets
  // a const ClassTypeInfo* update the shared values.
  mutable std::unordered_map<std::string, Logic4Vec> static_properties;

  std::unordered_map<std::string, uint64_t> enum_members;

  // §37.32: the class specializations that name this class definition as their
  // defining class; reported by the vpiClassTypespec iteration on a class defn.
  std::vector<const ClassTypespecInfo*> direct_specializations;

  int FindVTableIndex(std::string_view mname) const;

  bool IsA(const ClassTypeInfo* other) const;
};

struct ClassObject {
  const ClassTypeInfo* type = nullptr;
  std::unordered_map<std::string, Logic4Vec> properties;
  uint32_t ref_count = 0;

  // §18.14.1 object stability: every instance owns an independent RNG for its
  // randomization methods. The allocating context installs rng_seed when the
  // object is created -- drawn from the creating thread's stream when one is
  // running, or from the enclosing initialization RNG for objects built by a
  // static declaration initializer (when no thread is active). The generator
  // is materialized lazily on first use so two objects created in the same
  // order from the same starting state always replay the same seeds.
  uint32_t rng_seed = 0;
  std::mt19937 rng;
  bool rng_initialized = false;

  Logic4Vec GetProperty(std::string_view name, Arena& arena) const;

  void SetProperty(std::string_view name, const Logic4Vec& val);

  ModuleItem* ResolveVirtualMethod(
      std::string_view name, const ClassTypeInfo** owner_out = nullptr) const;

  ModuleItem* ResolveMethod(std::string_view name) const;

  // Resolves `name` starting at `from_type` and walking up the inheritance
  // chain. When `defining_type_out` is non-null, it receives the class in which
  // the method was found (its lexically enclosing class), so callers can track
  // the scope for a subsequent `super` resolution.
  ModuleItem* ResolveMethodForType(
      std::string_view name, const ClassTypeInfo* from_type,
      const ClassTypeInfo** defining_type_out = nullptr) const;

  Logic4Vec GetPropertyForType(std::string_view name,
                               const ClassTypeInfo* declared_type,
                               Arena& arena) const;

  void SetPropertyForType(std::string_view name,
                          const ClassTypeInfo* declared_type,
                          const Logic4Vec& val);

  ClassObject* ShallowCopy(Arena& arena) const;
};

// §37.32: a class typespec is either a purely lexical construct (a typespec
// written in source that names a class) or a class specialization (a concrete
// instantiation of a parameterized class). The two forms support different
// relations, so the kind is modeled explicitly.
enum class ClassTypespecKind : std::uint8_t {
  kLexical,
  kSpecialization,
};

// §37.32: one method visible from a class typespec. has_explicit_decl is false
// for built-in methods that were never declared in source; those are excluded
// when iterating the methods of a specialization.
struct ClassTypespecMethod {
  std::string_view name;
  bool is_static = false;
  bool has_explicit_decl = true;
};

// §37.32: one parameter visible from a class typespec. is_local_param is true
// for parameters declared in the class body (as opposed to the parameter port
// list); it is the value vpi_get(vpiLocalParam) reports for that parameter.
struct ClassTypespecParam {
  std::string_view name;
  bool is_local_param = false;
};

// §37.32: a parameter assignment for a class typespec. vpiRhs reports the
// explicit argument supplied at the specialization site when one is given, and
// otherwise falls back to the parameter's declared default.
struct ClassTypespecParamAssign {
  std::string_view name;
  bool has_explicit_arg = false;
  std::string_view explicit_rhs;
  std::string_view default_rhs;
};

// §37.32: a constraint visible from a class typespec. An inline constraint is
// not part of the typespec's constraint set; an external constraint is ordered
// by its prototype declaration rather than its out-of-body definition.
struct ClassTypespecConstraint {
  std::string_view name;
  bool is_inline = false;
  bool is_extern = false;
  int decl_order = 0;
  int prototype_order = 0;
};

// §37.32: a virtual interface variable of a class typespec. array_size greater
// than zero denotes an array of that many elements; zero denotes a scalar.
struct ClassTypespecVifVar {
  std::string_view name;
  int array_size = 0;
};

// §37.32: lightweight description of a class typespec sufficient to answer the
// VPI queries this clause defines. It reuses ClassTypeInfo for the class
// definition (which already carries the base-class chain and the built-in
// flag).
struct ClassTypespecInfo {
  std::string_view name;
  ClassTypespecKind kind = ClassTypespecKind::kLexical;

  // §37.32: declared lifetime, shared with §37.3.7. False => static.
  bool automatic = false;

  // §37.32: the defining class. May be a built-in class (class_defn then
  // reports NULL) or null when unknown.
  const ClassTypeInfo* class_defn = nullptr;

  // §37.32: the base class typespec this one extends, if any.
  const ClassTypespecInfo* extends = nullptr;

  std::vector<ClassTypespecMethod> methods;
  std::vector<ClassTypespecParam> params;
  std::vector<ClassTypespecConstraint> constraints;
  std::vector<ClassTypespecVifVar> vif_vars;
  std::vector<ClassTypespecParamAssign> param_assigns;
};

// §37.32: a lexical-only typespec does not support the member-collection
// relations (vpiVariables, vpiMethods, vpiConstraint, vpiNamedEvent,
// vpiNamedEventArray, vpiTypedef, vpiInternalScope). Only a specialization
// does.
bool VpiClassTypespecSupportsMembers(const ClassTypespecInfo& ts);

// §37.32: a specialization must carry a valid, non-empty (though tool-chosen)
// name.
bool VpiClassTypespecNameValid(const ClassTypespecInfo& ts);

// §37.32: the defining class returned by the vpiClassDefn relation, or nullptr
// for a built-in class.
const ClassTypeInfo* VpiClassDefnOf(const ClassTypeInfo& cls);

// §37.32: the base class typespec returned by vpiExtends, or nullptr when the
// typespec derives from nothing.
const ClassTypespecInfo* VpiExtendsOf(const ClassTypespecInfo& ts);

// §37.32: the base typespec of a specialization shall itself be a
// specialization. Returns true when this invariant holds for ts (vacuously true
// when ts has no base or ts is not a specialization).
bool VpiClassTypespecBaseIsSpecialization(const ClassTypespecInfo& ts);

// §37.32: the methods reported when iterating vpiMethods on a specialization:
// both static and automatic methods, but excluding built-in methods that have
// no explicit declaration.
std::vector<ClassTypespecMethod> VpiClassTypespecMethods(
    const ClassTypespecInfo& ts);

// §37.32: vpi_get(vpiLocalParam) for a class-typespec parameter -- true when
// the parameter was declared in the class body.
bool VpiClassTypespecParamIsLocal(const ClassTypespecParam& param);

// §37.32: the vpiRhs of a parameter assignment -- the explicit argument when
// one was supplied, otherwise the declared default.
std::string_view VpiClassTypespecParamRhs(const ClassTypespecParamAssign& pa);

// §37.32: a value read through a class typespec is only well defined for static
// members; a non-static member has no value until an instance is selected, so
// access via the typespec alone is disallowed for it.
bool VpiClassTypespecValueAccessAllowed(bool obtained_from_class_typespec,
                                        bool is_static);

// §37.32: the constraints reported when iterating a class typespec -- inline
// constraints are excluded, and the remaining constraints follow declaration
// order, with external constraints ordered by their prototype.
std::vector<ClassTypespecConstraint> VpiClassTypespecConstraints(
    const ClassTypespecInfo& ts);

// §37.32: the number of virtual interface variables when arrays are expanded to
// one entry per element.
int VpiClassTypespecVirtualInterfaceVarCount(const ClassTypespecInfo& ts);

// §37.32: the number of virtual interface variables when each array counts as a
// single collapsed variable.
int VpiClassTypespecArrayVarCount(const ClassTypespecInfo& ts);

// §37.32: the class specializations that directly name this class definition.
std::vector<const ClassTypespecInfo*> VpiClassDefnSpecializations(
    const ClassTypeInfo& cls);

inline constexpr uint64_t kNullClassHandle = 0;

struct WeakReference {
  uint64_t referent_handle = kNullClassHandle;

  uint64_t Get() const { return referent_handle; }

  void Clear() { referent_handle = kNullClassHandle; }

  static int64_t GetId(uint64_t obj_handle) {
    return (obj_handle == kNullClassHandle) ? 0
                                            : static_cast<int64_t>(obj_handle);
  }
};

}  // namespace delta
