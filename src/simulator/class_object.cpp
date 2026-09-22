#include "simulator/class_object.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

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

const ClassTypeInfo::PropertyInfo* ClassTypeInfo::FindProperty(
    std::string_view name) const {
  for (const auto* t = this; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return &prop;
    }
  }
  return nullptr;
}

const ClassTypeInfo* ClassTypeInfo::StaticPropertyDeclarer(
    std::string_view name) const {
  std::string key(name);
  for (const auto* t = this; t != nullptr; t = t->parent) {
    if (t->static_properties.find(key) != t->static_properties.end()) return t;
  }
  return nullptr;
}

const ClassTypeInfo* ClassTypeInfo::StaticPropertyOwner(
    std::string_view name) const {
  for (const auto* t = this; t != nullptr; t = t->enclosing) {
    const ClassTypeInfo* declarer = t->StaticPropertyDeclarer(name);
    if (declarer != nullptr) return declarer;
  }
  return nullptr;
}

// §8.13 (printed pages 189-190) with §8.9 (printed 186): a static property
// read through a handle is the declaring class's one storage, C's for a D
// object's `n` where D extends C, the same `c.n` through a C handle reads.
// Asked of the object's own class alone, `d.n` read 0 after `C::n = 5`.
Logic4Vec ClassObject::GetProperty(std::string_view name, Arena& arena) const {
  std::string key(name);
  auto it = properties.find(key);
  if (it != properties.end()) return it->second;
  const ClassTypeInfo* declarer =
      type != nullptr ? type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer != nullptr) return declarer->static_properties.find(key)->second;
  return MakeLogic4VecVal(arena, 32, 0);
}

// §5.7.1: what a property holds is its own value and no literal, so a 1-bit
// property set from `'1` holds a 1-bit 1 that zero-extends when read into a
// wider object; the flag that has the literal's value fill a resize stops at
// the store, as it does at a variable's (ResizeToWidth in
// statement_assign_select.cpp).
static Logic4Vec StoredPropertyValue(const Logic4Vec& val) {
  Logic4Vec stored = val;
  stored.fills_width = false;
  return stored;
}

void ClassObject::SetProperty(std::string_view name, const Logic4Vec& raw) {
  Logic4Vec val = StoredPropertyValue(raw);
  std::string key(name);
  // §8.13 with §8.9: the storage written is the declaring class's, C's for a
  // D object's `n` where D extends C, so the processes watching that class
  // (§9.4.2, `@(C::n)`) are the ones told. Asked of the object's own class
  // alone, `d.n = 7` landed in the object's map and `C::n` read 0.
  const ClassTypeInfo* declarer =
      type != nullptr ? type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer != nullptr) {
    declarer->static_properties[key] = val;
    declarer->NotifyStaticWatchers();
    return;
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

// Whether the bare key of `name` on this object is the storage `owner`
// declares: it is unless a class between the object's own type and `owner`,
// exclusive, declares `name` again and so shadows it (§8.15).
bool ClassObject::BareNameIsDeclaredBy(std::string_view name,
                                       const ClassTypeInfo* owner) const {
  for (const auto* t = type; t != nullptr && t != owner; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    if (properties.find(scoped) != properties.end()) return false;
  }
  return true;
}

// §8.15: a write from a method of `declared_type` lands on the declaration
// that class sees, its own or the nearest base's. The bare key, what a read
// through a handle answers, is kept in step whenever it names that same
// storage: a base constructor writing `v` on a derived object was reaching the
// scoped key alone, and `child.v` read the bare default of 0 afterwards.
void ClassObject::SetPropertyForType(std::string_view name,
                                     const ClassTypeInfo* declared_type,
                                     const Logic4Vec& raw) {
  Logic4Vec val = StoredPropertyValue(raw);
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) {
      it->second = val;
      if (BareNameIsDeclaredBy(name, t)) properties[std::string(name)] = val;
      return;
    }
  }
  SetProperty(name, val);
}

// §8.12: the entries and index type of `src` in an AssocArrayObject of the
// copy's own, each entry's words its own as OwnRhsWords makes them.
static AssocArrayObject* CopyAssocArray(const AssocArrayObject* src,
                                        Arena& arena) {
  auto* dst = arena.Create<AssocArrayObject>();
  dst->elem_width = src->elem_width;
  dst->index_width = src->index_width;
  dst->is_string_key = src->is_string_key;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  dst->is_index_signed = src->is_index_signed;
  dst->has_default = src->has_default;
  if (src->has_default)
    dst->default_value = OwnRhsWords(src->default_value, arena);
  dst->has_elem_init = src->has_elem_init;
  if (src->has_elem_init) dst->elem_init = OwnRhsWords(src->elem_init, arena);
  for (const auto& [key, val] : src->int_data)
    dst->int_data[key] = OwnRhsWords(val, arena);
  for (const auto& [key, val] : src->str_data)
    dst->str_data[key] = OwnRhsWords(val, arena);
  return dst;
}

// §8.12 (shallow copy, step 2) with §6.8: the copy's queue holds elements of
// its own, each with its own words for the reason ShallowCopy gives, under
// the width, state-ness and bound (§7.10.5) the declaration gave the property.
// §7.10.3 gives the copy's elements identities of their own: a reference taken
// on the source's element names the source's, not the copy's.
static QueueObject* CopyQueue(const QueueObject* src, Arena& arena) {
  auto* dst = arena.Create<QueueObject>();
  dst->elem_width = src->elem_width;
  dst->is_4state = src->is_4state;
  dst->max_size = src->max_size;
  dst->holds_class_handles = src->holds_class_handles;
  dst->elements.reserve(src->elements.size());
  for (const auto& elem : src->elements)
    dst->elements.push_back(OwnRhsWords(elem, arena));
  dst->AssignFreshIds();
  return dst;
}

ClassObject* ClassObject::ShallowCopy(Arena& arena) const {
  auto* copy = arena.Create<ClassObject>();
  copy->type = type;
  // §8.12 (shallow copy, step 2): "All class properties ... are copied to
  // the new object." A class property is a variable, and §6.8 has a variable
  // "store a value from one assignment to the next", so the copy's properties
  // are storage of their own: the two objects hold two values that happen to
  // start out equal. A map assignment copy-constructs each Logic4Vec, and a
  // Logic4Vec copy carries the words pointer rather than the words
  // (src/common/types.h), so it would leave every property of the copy naming
  // the source property's buffer -- one storage element under two objects,
  // which the in-place writers then expose: DepositBitField writes through the
  // words it finds rather than replacing them, so a packed-member deposit into
  // either object's property would be a deposit into both. Copy the words per
  // entry instead. What §8.12 does leave shared is the object a handle
  // property refers to, and that survives this: the handle is the property's
  // value, so copying the value copies the handle and both objects still name
  // the one object it refers to.
  for (const auto& [name, val] : properties)
    copy->properties[name] = OwnRhsWords(val, arena);
  // §8.12 (shallow copy, step 2) again: a property declared with an
  // associative dimension is a variable of the object like any other, so the
  // copy takes entries of its own, each with its own words for the reason
  // above, and the index type the declaration gave the property.
  for (const auto& [name, aa] : assoc_properties)
    copy->assoc_properties[name] = CopyAssocArray(aa, arena);
  // §8.12 (shallow copy, step 2) once more for a property declared with a
  // queue dimension: the copy's queue holds the source's elements at the time
  // of the copy and grows and shrinks on its own after it (§7.10).
  for (const auto& [name, q] : queue_properties)
    copy->queue_properties[name] = CopyQueue(q, arena);
  // §8.12 (shallow copy, step 2) for a semaphore or mailbox property: the
  // property is a handle to the built-in object (§15.3.1, §15.4.1), so the
  // copy names the same bucket or queue, as a copied class handle does.
  copy->semaphore_properties = semaphore_properties;
  copy->mailbox_properties = mailbox_properties;
  // §8.12 has the copy be of the same class, which for a parameterized class
  // is the same specialization (§8.25), so it is bound to the same types.
  copy->type_param_actuals = type_param_actuals;
  // §8.12: a shallow copy carries over the source object's internal
  // randomization state. The per-instance RNG (its seed and live generator
  // state) is duplicated into the new object so it resumes from where the
  // source left off rather than from a fresh, unseeded generator.
  copy->rng_seed = rng_seed;
  copy->rng = rng;
  copy->rng_initialized = rng_initialized;
  // §8.12 (shallow copy, step 2): the internal states used for randomization
  // are also copied. Besides the RNG that means the constraint_mode status of
  // each constraint block (§18.9), the rand_mode status of each random variable
  // (§18.8), and the cyclic state of randc variables (§18.4.2). The two mode
  // maps are plain value maps, so a map copy duplicates them. The randc history
  // is held behind shared_ptr; the copy must be an independent per-object cycle
  // (the source and the copy each advance their own permutation), so each set
  // is cloned into a fresh shared_ptr rather than aliasing the source's.
  copy->constraint_active = constraint_active;
  copy->rand_active = rand_active;
  for (const auto& [member, history] : randc_history) {
    copy->randc_history[member] =
        std::make_shared<std::unordered_set<int64_t>>(*history);
  }
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

ClassTypespecInfo VpiClassTypespecOf(const ClassTypeInfo* type) {
  ClassTypespecInfo ts;
  if (type == nullptr || type->decl == nullptr) return ts;
  ts.name = type->name;
  ts.kind = ClassTypespecKind::kSpecialization;
  ts.class_defn = type;
  for (const auto& [pname, pexpr] : type->decl->params) {
    ts.params.push_back(
        {pname, type->decl->localparam_port_names.count(pname) != 0});
    ClassTypespecParamAssign pa;
    pa.name = pname;
    auto held = type->static_properties.find(std::string(pname));
    if (held != type->static_properties.end()) {
      pa.has_bound_value = true;
      pa.bound_value = held->second;
    }
    ts.param_assigns.push_back(pa);
  }
  return ts;
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

std::string_view MemberClassTypeName(const ClassTypeInfo* type,
                                     std::string_view field) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == field)
        return m->data_type.type_name;
    }
  }
  return {};
}

}  // namespace delta
