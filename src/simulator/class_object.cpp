#include "simulator/class_object.h"

#include <algorithm>

#include "common/arena.h"
#include "parser/ast.h"

namespace delta {

int ClassTypeInfo::FindVTableIndex(std::string_view mname) const {
  for (size_t i = 0; i < vtable.size(); ++i) {
    if (vtable[i].method_name == mname) return static_cast<int>(i);
  }
  return -1;
}

bool ClassTypeInfo::IsA(const ClassTypeInfo* other) const {
  for (const auto* cur = this; cur != nullptr; cur = cur->parent) {
    if (cur == other) return true;
    for (const auto* iface : cur->extended_interfaces) {
      if (iface && iface->IsA(other)) return true;
    }
  }
  return false;
}

Logic4Vec ClassObject::GetProperty(std::string_view name, Arena& arena) const {
  std::string key(name);
  auto it = properties.find(key);
  if (it != properties.end()) return it->second;
  if (type) {
    auto sit = type->static_properties.find(key);
    if (sit != type->static_properties.end()) return sit->second;
  }
  return MakeLogic4VecVal(arena, 32, 0);
}

void ClassObject::SetProperty(std::string_view name, const Logic4Vec& val) {
  std::string key(name);
  if (type) {
    auto it = type->static_properties.find(key);
    if (it != type->static_properties.end()) {
      it->second = val;
      return;
    }
  }
  properties[key] = val;
}

ModuleItem* ClassObject::ResolveVirtualMethod(
    std::string_view name, const ClassTypeInfo** owner_out) const {
  if (!type) return nullptr;
  int idx = type->FindVTableIndex(name);
  if (idx >= 0) {
    const auto& entry = type->vtable[static_cast<size_t>(idx)];
    if (owner_out) *owner_out = entry.owner;
    return entry.method;
  }
  return nullptr;
}

ModuleItem* ClassObject::ResolveMethod(std::string_view name) const {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(name));
    if (it != t->methods.end()) return it->second;
  }
  return nullptr;
}

ModuleItem* ClassObject::ResolveMethodForType(
    std::string_view name, const ClassTypeInfo* from_type,
    const ClassTypeInfo** defining_type_out) const {
  for (const auto* t = from_type; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(name));
    if (it != t->methods.end()) {
      if (defining_type_out) *defining_type_out = t;
      return it->second;
    }
  }
  return nullptr;
}

Logic4Vec ClassObject::GetPropertyForType(std::string_view name,
                                          const ClassTypeInfo* declared_type,
                                          Arena& arena) const {
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) return it->second;
  }
  return GetProperty(name, arena);
}

void ClassObject::SetPropertyForType(std::string_view name,
                                     const ClassTypeInfo* declared_type,
                                     const Logic4Vec& val) {
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) {
      it->second = val;

      if (declared_type == type) properties[std::string(name)] = val;
      return;
    }
  }
  SetProperty(name, val);
}

ClassObject* ClassObject::ShallowCopy(Arena& arena) const {
  auto* copy = arena.Create<ClassObject>();
  copy->type = type;
  copy->properties = properties;
  // §8.12: a shallow copy carries over the source object's internal
  // randomization state. The per-instance RNG (its seed and live generator
  // state) is duplicated into the new object so it resumes from where the
  // source left off rather than from a fresh, unseeded generator.
  copy->rng_seed = rng_seed;
  copy->rng = rng;
  copy->rng_initialized = rng_initialized;
  return copy;
}

// §37.32: only a specialization exposes the member-collection relations; a
// purely lexical typespec answers them as empty/unsupported.
bool VpiClassTypespecSupportsMembers(const ClassTypespecInfo& ts) {
  return ts.kind == ClassTypespecKind::kSpecialization;
}

// §37.32: a specialization must have a non-empty name; for any other kind the
// name is not required to be meaningful.
bool VpiClassTypespecNameValid(const ClassTypespecInfo& ts) {
  if (ts.kind != ClassTypespecKind::kSpecialization) return true;
  return !ts.name.empty();
}

// §37.32: built-in classes report no defining class.
const ClassTypeInfo* VpiClassDefnOf(const ClassTypeInfo& cls) {
  if (cls.is_builtin) return nullptr;
  return &cls;
}

// §37.32: the base class typespec, or nullptr if none.
const ClassTypespecInfo* VpiExtendsOf(const ClassTypespecInfo& ts) {
  return ts.extends;
}

// §37.32: the base typespec of a specialization is required to also be a
// specialization. The check is vacuously satisfied when there is no base or
// when ts is not itself a specialization.
bool VpiClassTypespecBaseIsSpecialization(const ClassTypespecInfo& ts) {
  if (ts.kind != ClassTypespecKind::kSpecialization) return true;
  if (ts.extends == nullptr) return true;
  return ts.extends->kind == ClassTypespecKind::kSpecialization;
}

// §37.32: iterating methods yields both static and automatic methods but drops
// built-in methods that were never explicitly declared.
std::vector<ClassTypespecMethod> VpiClassTypespecMethods(
    const ClassTypespecInfo& ts) {
  std::vector<ClassTypespecMethod> result;
  if (ts.kind != ClassTypespecKind::kSpecialization) return result;
  for (const ClassTypespecMethod& m : ts.methods) {
    if (m.has_explicit_decl) result.push_back(m);
  }
  return result;
}

// §37.32: vpiLocalParam is true exactly for parameters declared in the class
// body.
bool VpiClassTypespecParamIsLocal(const ClassTypespecParam& param) {
  return param.is_local_param;
}

// §37.32: an explicit argument overrides the declared default for vpiRhs.
std::string_view VpiClassTypespecParamRhs(const ClassTypespecParamAssign& pa) {
  return pa.has_explicit_arg ? pa.explicit_rhs : pa.default_rhs;
}

// §37.32: reading a value through the typespec is allowed unless the member is
// a non-static member reached only via the typespec.
bool VpiClassTypespecValueAccessAllowed(bool obtained_from_class_typespec,
                                        bool is_static) {
  return !obtained_from_class_typespec || is_static;
}

// §37.32: drop inline constraints, then order the rest by declaration order,
// using the prototype order for external constraints.
std::vector<ClassTypespecConstraint> VpiClassTypespecConstraints(
    const ClassTypespecInfo& ts) {
  std::vector<ClassTypespecConstraint> result;
  for (const ClassTypespecConstraint& c : ts.constraints) {
    if (!c.is_inline) result.push_back(c);
  }
  std::stable_sort(
      result.begin(), result.end(),
      [](const ClassTypespecConstraint& a, const ClassTypespecConstraint& b) {
        int ea = a.is_extern ? a.prototype_order : a.decl_order;
        int eb = b.is_extern ? b.prototype_order : b.decl_order;
        return ea < eb;
      });
  return result;
}

// §37.32: expanding arrays counts each element of a virtual interface array as
// a separate variable; scalars count once.
int VpiClassTypespecVirtualInterfaceVarCount(const ClassTypespecInfo& ts) {
  int total = 0;
  for (const ClassTypespecVifVar& v : ts.vif_vars) {
    total += (v.array_size > 0) ? v.array_size : 1;
  }
  return total;
}

// §37.32: collapsing arrays counts each virtual interface variable once,
// regardless of array size.
int VpiClassTypespecArrayVarCount(const ClassTypespecInfo& ts) {
  return static_cast<int>(ts.vif_vars.size());
}

// §37.32: the specializations directly naming this class definition.
std::vector<const ClassTypespecInfo*> VpiClassDefnSpecializations(
    const ClassTypeInfo& cls) {
  return cls.direct_specializations;
}

}  // namespace delta
