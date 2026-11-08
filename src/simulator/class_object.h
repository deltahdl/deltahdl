#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

struct AssocArrayObject;
struct MailboxObject;
struct QueueObject;
struct SemaphoreObject;
struct Variable;
struct ClassDecl;
struct ClassMember;
struct ConstraintForeachRef;
struct DataType;
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
  bool is_builtin = false;
  std::vector<const ClassTypeInfo*> extended_interfaces;
  const ClassTypeInfo* enclosing = nullptr;
  std::string_view package;
  std::string_view instance_scope;
  const std::vector<DataType>* param_actuals = nullptr;
  const std::unordered_map<std::string_view, int64_t>* unit_constants = nullptr;

  struct PropertyInfo {
    std::string_view name;
    uint32_t width = 32;
    bool is_static = false;
    bool is_local = false;
    bool is_protected = false;
    bool is_const = false;
    Expr* init_expr = nullptr;
    bool is_4state = false;
    bool width_is_declared = false;
    bool is_real = false;
    bool is_string = false;
    bool is_signed = false;
    std::string_view type_name = {};
    bool is_virtual_interface = false;
    uint32_t array_size = 0;
    int64_t array_lo = 0;
    bool array_descending = false;
    bool is_dynamic = false;
    std::vector<uint32_t> dim_los = {};
    std::vector<uint32_t> dim_sizes = {};
    std::vector<bool> dim_descending = {};

    bool IsArray() const { return array_size > 0 || is_dynamic; }
  };
  std::vector<PropertyInfo> properties;

  std::unordered_map<std::string, ModuleItem*> methods;

  std::vector<VTableEntry> vtable;

  mutable std::unordered_map<std::string, Logic4Vec> static_properties;

  mutable std::unordered_map<std::string, AssocArrayObject*>
      static_assoc_properties;

  mutable std::unordered_map<std::string, QueueObject*> static_queue_properties;

  mutable std::unordered_map<std::string, SemaphoreObject*>
      static_semaphore_properties;
  mutable std::unordered_map<std::string, MailboxObject*>
      static_mailbox_properties;
  mutable std::unordered_map<std::string, Variable*> static_event_properties;

  mutable std::unordered_map<std::string, bool> static_constraint_active;

  mutable std::unordered_map<std::string, bool> static_rand_active;

  mutable std::unordered_map<std::string,
                             std::shared_ptr<std::unordered_set<int64_t>>>
      static_randc_history;
  mutable std::unordered_map<std::string, std::shared_ptr<std::vector<int64_t>>>
      static_randc_domain;

  std::unordered_map<std::string, uint64_t> enum_members;

  struct ForeachInstances {
    uint32_t count = 0;
    std::vector<Expr*> relations;
  };
  mutable std::unordered_map<const ConstraintForeachRef*, ForeachInstances>
      foreach_instances;

  mutable std::unordered_map<const Expr*, Expr*> size_resolved_relations;

  std::vector<const ClassTypespecInfo*> direct_specializations;

  mutable std::vector<std::function<bool()>> static_watchers;

  void AddStaticWatcher(std::function<bool()> cb) const {
    static_watchers.push_back(std::move(cb));
  }

  void NotifyStaticWatchers() const {
    auto pending = std::move(static_watchers);
    for (auto& cb : pending) {
      if (!cb()) static_watchers.push_back(std::move(cb));
    }
  }

  int FindVTableIndex(std::string_view mname) const;

  bool IsA(const ClassTypeInfo* other) const;

  const PropertyInfo* FindProperty(std::string_view name) const;

  const ClassTypeInfo* StaticPropertyDeclarer(std::string_view name) const;

  const ClassTypeInfo* StaticPropertyOwner(std::string_view name) const;

  struct EnumLiteralShape {
    uint32_t width = 32;
    bool is_signed = false;
  };
  std::unordered_map<std::string, EnumLiteralShape> enum_literal_shapes;
};

inline constexpr uint64_t kNullClassHandle = 0;

struct ClassObject {
  const ClassTypeInfo* type = nullptr;
  std::string instance;
  std::unordered_map<std::string, Logic4Vec> properties;
  std::unordered_map<std::string, AssocArrayObject*> assoc_properties;
  std::unordered_map<std::string, QueueObject*> queue_properties;
  std::unordered_map<std::string, SemaphoreObject*> semaphore_properties;
  std::unordered_map<std::string, MailboxObject*> mailbox_properties;
  std::unordered_map<std::string, Variable*> event_properties;
  std::unordered_map<std::string, const DataType*> type_param_actuals;
  std::unordered_set<std::string> unbounded_params;
  std::vector<std::function<bool()>> watchers;

  void AddWatcher(std::function<bool()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    auto pending = std::move(watchers);
    for (auto& cb : pending) {
      if (!cb()) watchers.push_back(std::move(cb));
    }
  }

  uint32_t ref_count = 0;

  uint64_t handle = kNullClassHandle;

  uint32_t rng_seed = 0;
  std::mt19937 rng;
  bool rng_initialized = false;

  std::unordered_map<std::string, bool> constraint_active;

  std::unordered_map<std::string, bool> rand_active;

  std::unordered_map<std::string, std::shared_ptr<std::unordered_set<int64_t>>>
      randc_history;
  std::unordered_map<std::string, std::shared_ptr<std::vector<int64_t>>>
      randc_domain;

  std::unordered_map<std::string, std::string> property_tags;

  struct RefCell {
    Variable* var = nullptr;
    uint32_t holders = 0;
  };
  std::unordered_map<std::string, RefCell> ref_cells;
  Variable* AcquireRefCell(std::string_view name, Arena& arena);
  void ReleaseRefCell(std::string_view name);

  const Logic4Vec* FindPropertyValue(std::string_view name) const;

  Logic4Vec GetProperty(std::string_view name, Arena& arena) const;

  void SetProperty(std::string_view name, const Logic4Vec& raw);

  ModuleItem* ResolveVirtualMethod(
      std::string_view name, const ClassTypeInfo** owner_out = nullptr) const;

  ModuleItem* ResolveMethod(std::string_view name) const;

  ModuleItem* ResolveMethodForType(
      std::string_view name, const ClassTypeInfo* from_type,
      const ClassTypeInfo** defining_type_out = nullptr) const;

  Logic4Vec GetPropertyForType(std::string_view name,
                               const ClassTypeInfo* declared_type,
                               Arena& arena) const;

  bool BareNameIsDeclaredBy(std::string_view name,
                            const ClassTypeInfo* owner) const;
  void SetPropertyForType(std::string_view name,
                          const ClassTypeInfo* declared_type,
                          const Logic4Vec& raw);

  ClassObject* ShallowCopy(Arena& arena) const;
};

enum class ClassTypespecKind : std::uint8_t {
  kLexical,
  kSpecialization,
};

struct ClassTypespecMethod {
  std::string_view name;
  bool is_static = false;
  bool has_explicit_decl = true;
};

struct ClassTypespecParam {
  std::string_view name;
  bool is_local_param = false;
};

struct ClassTypespecParamAssign {
  std::string_view name;
  bool has_explicit_arg = false;
  std::string_view explicit_rhs;
  std::string_view default_rhs;
  bool has_bound_value = false;
  Logic4Vec bound_value;
};

struct ClassTypespecConstraint {
  std::string_view name;
  bool is_inline = false;
  bool is_extern = false;
  int decl_order = 0;
  int prototype_order = 0;
};

struct ClassTypespecVifVar {
  std::string_view name;
  int array_size = 0;
};

struct ClassTypespecInfo {
  std::string_view name;
  ClassTypespecKind kind = ClassTypespecKind::kLexical;

  bool automatic = false;

  const ClassTypeInfo* class_defn = nullptr;

  const ClassTypespecInfo* extends = nullptr;

  std::vector<ClassTypespecMethod> methods;
  std::vector<ClassTypespecParam> params;
  std::vector<ClassTypespecConstraint> constraints;
  std::vector<ClassTypespecVifVar> vif_vars;
  std::vector<ClassTypespecParamAssign> param_assigns;
};

bool VpiClassTypespecSupportsMembers(const ClassTypespecInfo& ts);

bool VpiClassTypespecNameValid(const ClassTypespecInfo& ts);

const ClassTypeInfo* VpiClassDefnOf(const ClassTypeInfo& cls);

const ClassTypespecInfo* VpiExtendsOf(const ClassTypespecInfo& ts);

bool VpiClassTypespecBaseIsSpecialization(const ClassTypespecInfo& ts);

std::vector<ClassTypespecMethod> VpiClassTypespecMethods(
    const ClassTypespecInfo& ts);

bool VpiClassTypespecParamIsLocal(const ClassTypespecParam& param);

std::string_view VpiClassTypespecParamRhs(const ClassTypespecParamAssign& pa);

ClassTypespecInfo VpiClassTypespecOf(const ClassTypeInfo* type);

bool VpiClassTypespecValueAccessAllowed(bool obtained_from_class_typespec,
                                        bool is_static);

std::vector<ClassTypespecConstraint> VpiClassTypespecConstraints(
    const ClassTypespecInfo& ts);

int VpiClassTypespecVirtualInterfaceVarCount(const ClassTypespecInfo& ts);

int VpiClassTypespecArrayVarCount(const ClassTypespecInfo& ts);

std::vector<const ClassTypespecInfo*> VpiClassDefnSpecializations(
    const ClassTypeInfo& cls);

std::string_view MemberClassTypeName(const ClassTypeInfo* type,
                                     std::string_view field);

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
