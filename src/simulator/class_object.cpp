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
#include "simulator/variable.h"

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

const Logic4Vec* ClassObject::FindPropertyValue(std::string_view name) const {
  std::string key(name);
  if (auto cell = ref_cells.find(key); cell != ref_cells.end())
    return &cell->second.var->value;
  auto it = properties.find(key);
  return it != properties.end() ? &it->second : nullptr;
}

Variable* ClassObject::AcquireRefCell(std::string_view name, Arena& arena) {
  std::string key(name);
  auto it = ref_cells.find(key);
  if (it == ref_cells.end()) {
    auto* var = arena.Create<Variable>();
    var->value = GetProperty(name, arena);
    it = ref_cells.emplace(key, RefCell{var, 0}).first;
  }
  ++it->second.holders;
  return it->second.var;
}

void ClassObject::ReleaseRefCell(std::string_view name) {
  auto it = ref_cells.find(std::string(name));
  if (it == ref_cells.end() || --it->second.holders > 0) return;
  Logic4Vec held = it->second.var->value;
  ref_cells.erase(it);
  SetPropertyForType(name, type, held);
}

Logic4Vec ClassObject::GetProperty(std::string_view name, Arena& arena) const {
  std::string key(name);
  if (const Logic4Vec* held = FindPropertyValue(key)) return *held;
  const ClassTypeInfo* declarer =
      type != nullptr ? type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer != nullptr) return declarer->static_properties.find(key)->second;
  return MakeLogic4VecVal(arena, 32, 0);
}

static Logic4Vec StoredPropertyValue(const Logic4Vec& val) {
  Logic4Vec stored = val;
  stored.fills_width = false;
  return stored;
}

void ClassObject::SetProperty(std::string_view name, const Logic4Vec& raw) {
  Logic4Vec val = StoredPropertyValue(raw);
  std::string key(name);
  const ClassTypeInfo* declarer =
      type != nullptr ? type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer != nullptr) {
    declarer->static_properties[key] = val;
    declarer->NotifyStaticWatchers();
    return;
  }
  properties[key] = val;
  if (auto cell = ref_cells.find(key); cell != ref_cells.end())
    cell->second.var->value = val;
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
    if (it == properties.end()) continue;
    auto cell = ref_cells.find(std::string(name));
    if (cell != ref_cells.end() && BareNameIsDeclaredBy(name, t))
      return cell->second.var->value;
    return it->second;
  }
  return GetProperty(name, arena);
}

bool ClassObject::BareNameIsDeclaredBy(std::string_view name,
                                       const ClassTypeInfo* owner) const {
  for (const auto* t = type; t != nullptr && t != owner; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    if (properties.find(scoped) != properties.end()) return false;
  }
  return true;
}

void ClassObject::SetPropertyForType(std::string_view name,
                                     const ClassTypeInfo* declared_type,
                                     const Logic4Vec& raw) {
  Logic4Vec val = StoredPropertyValue(raw);
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) {
      it->second = val;
      if (BareNameIsDeclaredBy(name, t)) SetProperty(name, val);
      return;
    }
  }
  SetProperty(name, val);
}

static AssocArrayObject* CopyAssocArray(const AssocArrayObject* src,
                                        Arena& arena) {
  auto* dst = arena.Create<AssocArrayObject>();
  dst->elem_width = src->elem_width;
  dst->index_width = src->index_width;
  dst->is_string_key = src->is_string_key;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  dst->is_signed = src->is_signed;
  dst->is_index_signed = src->is_index_signed;
  dst->index_class = src->index_class;
  dst->index_type_name = src->index_type_name;
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

static QueueObject* CopyQueue(const QueueObject* src, Arena& arena) {
  auto* dst = arena.Create<QueueObject>();
  dst->elem_width = src->elem_width;
  dst->is_4state = src->is_4state;
  dst->is_signed = src->is_signed;
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
  copy->instance = instance;
  for (const auto& [name, val] : properties)
    copy->properties[name] = OwnRhsWords(val, arena);
  for (const auto& [name, aa] : assoc_properties)
    copy->assoc_properties[name] = CopyAssocArray(aa, arena);
  for (const auto& [name, q] : queue_properties)
    copy->queue_properties[name] = CopyQueue(q, arena);
  copy->semaphore_properties = semaphore_properties;
  copy->event_properties = event_properties;
  copy->mailbox_properties = mailbox_properties;
  copy->property_tags = property_tags;
  copy->type_param_actuals = type_param_actuals;
  copy->rng_seed = rng_seed;
  copy->rng = rng;
  copy->rng_initialized = rng_initialized;
  copy->constraint_active = constraint_active;
  copy->rand_active = rand_active;
  for (const auto& [member, history] : randc_history) {
    copy->randc_history[member] =
        std::make_shared<std::unordered_set<int64_t>>(*history);
  }
  for (const auto& [member, domain] : randc_domain) {
    copy->randc_domain[member] =
        std::make_shared<std::vector<int64_t>>(*domain);
  }
  return copy;
}

bool VpiClassTypespecSupportsMembers(const ClassTypespecInfo& ts) {
  return ts.kind == ClassTypespecKind::kSpecialization;
}

bool VpiClassTypespecNameValid(const ClassTypespecInfo& ts) {
  if (ts.kind != ClassTypespecKind::kSpecialization) return true;
  return !ts.name.empty();
}

const ClassTypeInfo* VpiClassDefnOf(const ClassTypeInfo& cls) {
  if (cls.is_builtin) return nullptr;
  return &cls;
}

const ClassTypespecInfo* VpiExtendsOf(const ClassTypespecInfo& ts) {
  return ts.extends;
}

bool VpiClassTypespecBaseIsSpecialization(const ClassTypespecInfo& ts) {
  if (ts.kind != ClassTypespecKind::kSpecialization) return true;
  if (ts.extends == nullptr) return true;
  return ts.extends->kind == ClassTypespecKind::kSpecialization;
}

std::vector<ClassTypespecMethod> VpiClassTypespecMethods(
    const ClassTypespecInfo& ts) {
  std::vector<ClassTypespecMethod> result;
  if (ts.kind != ClassTypespecKind::kSpecialization) return result;
  for (const ClassTypespecMethod& m : ts.methods) {
    if (m.has_explicit_decl) result.push_back(m);
  }
  return result;
}

bool VpiClassTypespecParamIsLocal(const ClassTypespecParam& param) {
  return param.is_local_param;
}

std::string_view VpiClassTypespecParamRhs(const ClassTypespecParamAssign& pa) {
  return pa.has_explicit_arg ? pa.explicit_rhs : pa.default_rhs;
}

ClassTypespecInfo VpiClassTypespecOf(const ClassTypeInfo* type) {
  ClassTypespecInfo ts;
  if (type == nullptr || type->decl == nullptr) return ts;
  ts.name = type->name;
  ts.kind = ClassTypespecKind::kSpecialization;
  ts.class_defn = type;
  const auto kAdd = [&ts, type](std::string_view pname, bool local) {
    ts.params.push_back({pname, local});
    ClassTypespecParamAssign pa;
    pa.name = pname;
    auto held = type->static_properties.find(std::string(pname));
    if (held != type->static_properties.end()) {
      pa.has_bound_value = true;
      pa.bound_value = held->second;
    }
    ts.param_assigns.push_back(pa);
  };
  for (const auto& [pname, pexpr] : type->decl->params) {
    kAdd(pname, type->decl->localparam_port_names.count(pname) != 0);
  }
  for (const ClassMember* member : type->decl->members) {
    if (member->kind == ClassMemberKind::kProperty && member->is_param) {
      kAdd(member->name, true);
    }
  }
  return ts;
}

bool VpiClassTypespecValueAccessAllowed(bool obtained_from_class_typespec,
                                        bool is_static) {
  return !obtained_from_class_typespec || is_static;
}

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

int VpiClassTypespecVirtualInterfaceVarCount(const ClassTypespecInfo& ts) {
  int total = 0;
  for (const ClassTypespecVifVar& v : ts.vif_vars) {
    total += (v.array_size > 0) ? v.array_size : 1;
  }
  return total;
}

int VpiClassTypespecArrayVarCount(const ClassTypespecInfo& ts) {
  return static_cast<int>(ts.vif_vars.size());
}

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
