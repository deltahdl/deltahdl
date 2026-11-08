#include "simulator/vpi_class_objects.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int PropertyVariableKind(const ClassMember& member, SimContext& ctx) {
  if (!member.unpacked_dims.empty()) {
    return member.data_type.kind == DataTypeKind::kEvent ? vpiNamedEventArray
                                                         : vpiArrayVar;
  }
  const DataType& type = member.data_type;
  const std::string kKey =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  const bool kNamesClass =
      type.kind == DataTypeKind::kNamed && ctx.FindClassType(kKey) != nullptr;
  return kNamesClass ? vpiClassVar : VpiDataTypeVariableKind(type.kind);
}

void MakeVifArrayElements(VpiObject* var, const VpiAttachBuild& build) {
  std::vector<std::string> names{std::string(var->name)};
  for (const std::vector<int>& dim : var->array_dim_indices) {
    std::vector<std::string> next;
    next.reserve(names.size() * dim.size());
    for (const std::string& name : names) {
      for (const int kIndex : dim) {
        next.push_back(name + "[" + std::to_string(kIndex) + "]");
      }
    }
    names = std::move(next);
  }
  for (std::string& name : names) {
    VpiObject* elem = build.alloc();
    elem->type = vpiVirtualInterfaceVar;
    elem->name = build.keep(std::move(name));
    elem->parent = var;
    var->children.push_back(elem);
  }
}

void CopyDeclaredClassTypespec(VpiObject& var, const VpiObject* defn,
                               const VpiAttachBuild& build) {
  if (var.type != vpiClassVar || defn == nullptr) return;
  for (const VpiObject* declared : defn->children) {
    if (declared->type != vpiClassVar || declared->name != var.name) continue;
    for (const VpiObject* typespec : declared->children) {
      VpiObject* copy = build.alloc();
      *copy = *typespec;
      copy->parent = &var;
      var.children.push_back(copy);
    }
  }
}

VpiObject* MakePropertyVariable(VpiObject* holder, ClassObject& obj,
                                const ClassMember& member, SimContext& ctx,
                                const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = PropertyVariableKind(member, ctx);
  VpiRecordWrittenDims(*var, member.unpacked_dims, ctx);
  var->name = build.keep(std::string(member.name));
  var->parent = holder;
  var->automatic = !member.is_static;
  var->alloc_scheme = VpiAllocSchemeFor(
      member.is_static ? VpiAllocKind::kOther : VpiAllocKind::kDynamic);
  if (member.is_local) {
    var->decl_facts.visibility = vpiLocalVis;
  } else if (member.is_protected) {
    var->decl_facts.visibility = vpiProtectedVis;
  }
  VpiRecordPropertyDecl(*var, member);
  var->property_of = &obj;
  if (member.data_type.kind == DataTypeKind::kVirtualInterface &&
      !member.unpacked_dims.empty()) {
    MakeVifArrayElements(var, build);
  }
  const Logic4Vec* held = VpiHeldPropertyValue(obj, member.name);
  if (held != nullptr) {
    auto* storage = build.arena.Create<Variable>();
    storage->value = MakeLogic4Vec(build.arena, held->width);
    storage->value.is_signed = held->is_signed;
    var->var = storage;
    var->size = static_cast<int>(held->width);
    VpiRefreshElementCopy(*var);
  }
  holder->children.push_back(var);
  return var;
}

std::vector<const ClassTypeInfo*> ClassChain(const ClassTypeInfo* type) {
  constexpr int kMaxDepth = 64;
  std::vector<const ClassTypeInfo*> chain;
  for (int depth = 0; depth < kMaxDepth && type != nullptr; ++depth) {
    chain.insert(chain.begin(), type);
    type = type->parent;
  }
  return chain;
}

VpiObject* ClassDefnOf(
    const ClassTypeInfo* type, std::string_view instance,
    const VpiObjectMap& objects,
    const std::unordered_map<const void*, VpiObject*>& by_decl) {
  if (type == nullptr || type->decl == nullptr) return nullptr;
  std::string_view path = instance;
  if (!path.empty() && path.back() == '.') path.remove_suffix(1);
  VpiObject* scope = type->package.empty() && !path.empty()
                         ? FindObjectForFlatName(objects, path)
                         : nullptr;
  if (scope != nullptr) {
    for (VpiObject* child : scope->children) {
      if (child->type == vpiClassDefn && child->name == type->decl->name) {
        return child;
      }
    }
  }
  auto found = by_decl.find(type->decl);
  return found == by_decl.end() ? nullptr : found->second;
}

struct ChainClass {
  const ClassTypeInfo* type;
  VpiObject* defn;
};

struct ObjectConstraintSite {
  VpiObject* holder;
  ClassObject& obj;
  const std::vector<ChainClass>& chain;
  const VpiClassObjDefn& of;
};

void MakeObjectConstraints(const ObjectConstraintSite& at,
                           const VpiConstraintNames& names,
                           const VpiAttachBuild& build) {
  for (const ChainClass& cls : at.chain) {
    const VpiClassCallSite& site = at.of.calls(cls.defn);
    const VpiCallStand kStand{at.holder, site.mod, site.package};
    const VpiConstraintNames kNames{names.objects, names.prefix, names.gen,
                                    names.scope,   names.ctx,    names.attrs,
                                    &kStand};
    for (const ClassMember* member : cls.type->decl->members) {
      if (member == nullptr || member->kind != ClassMemberKind::kConstraint) {
        continue;
      }
      VpiObject* constraint =
          VpiMakeConstraint(*member, at.holder, kNames, build);
      constraint->constraint_of = &at.obj;
      at.holder->children.push_back(constraint);
    }
  }
}

void RelateObjectMethods(VpiObject* holder,
                         const std::vector<ChainClass>& chain) {
  std::unordered_set<std::string_view> named;
  for (auto cls = chain.rbegin(); cls != chain.rend(); ++cls) {
    if (cls->defn == nullptr) continue;
    for (VpiObject* child : cls->defn->children) {
      if (VpiIsClassMethodType(child->type) &&
          named.insert(child->name).second) {
        holder->children.push_back(child);
      }
    }
  }
}

int MessageConstType(const MailboxMessageType& type) {
  switch (type.value_kind) {
    case MailboxMessageType::Kind::kReal:
      return vpiRealConst;
    case MailboxMessageType::Kind::kString:
      return vpiStringConst;
    default:
      return vpiBinaryConst;
  }
}

VpiObject* ClassObjTypespec(const ClassTypeInfo& type, VpiObject* defn,
                            VpiObject* made, const VpiAttachBuild& build) {
  if (defn != nullptr) {
    if (VpiObject* held = VpiSpecializationTypespec(*defn, type.name)) {
      return held;
    }
  }
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(type.name));
  typespec->parent = made;
  if (defn != nullptr) typespec->children.push_back(defn);
  return typespec;
}

}  // namespace

VpiObject* VpiMakeObjectParameter(VpiObject* holder, const ClassDecl& decl,
                                  const ClassTypespecParam& param,
                                  const ClassTypespecParamAssign& assign,
                                  const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  const bool kType = decl.type_param_names.contains(param.name);
  made->type = kType ? vpiTypeParameter : vpiParameter;
  made->name = build.keep(std::string(param.name));
  made->parent = holder;
  made->local_param = param.is_local_param;
  if (!kType) {
    auto* storage = build.arena.Create<Variable>();
    storage->value = assign.bound_value;
    made->var = storage;
    made->size = static_cast<int>(assign.bound_value.width);
  }
  holder->children.push_back(made);
  return made;
}

void VpiRecordPropertyDecl(VpiObject& var, const ClassMember& member) {
  if (member.is_randc) {
    var.rand_type = vpiRandC;
  } else {
    var.rand_type = member.is_rand ? vpiRand : vpiNotRand;
  }
  var.decl_facts.constant_variable =
      member.is_const || member.data_type.is_const;
  var.is_modport = !member.data_type.modport_name.empty();
}

Logic4Vec* VpiHeldPropertyValue(ClassObject& obj, std::string_view name) {
  std::string key(name);
  if (auto cell = obj.ref_cells.find(key); cell != obj.ref_cells.end()) {
    return &cell->second.var->value;
  }
  if (auto own = obj.properties.find(key); own != obj.properties.end()) {
    return &own->second;
  }
  const ClassTypeInfo* declarer =
      obj.type != nullptr ? obj.type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer == nullptr) return nullptr;
  auto found = declarer->static_properties.find(key);
  return found == declarer->static_properties.end() ? nullptr : &found->second;
}

VpiObject* VpiMakeClassObject(ClassObject& obj, const VpiClassObjDefn& of,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  made->type = vpiClassObj;
  made->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kDynamic);
  made->obj_id = static_cast<int64_t>(obj.handle);
  if (obj.type == nullptr) return made;
  made->children.push_back(
      ClassObjTypespec(*obj.type, of.defn_of(*obj.type), made, build));
  const ClassTypespecInfo kTypespec = VpiClassTypespecOf(obj.type);
  for (std::size_t i = 0; i < kTypespec.params.size(); ++i) {
    VpiMakeObjectParameter(made, *obj.type->decl, kTypespec.params[i],
                           kTypespec.param_assigns[i], build);
  }
  std::vector<ChainClass> chain;
  for (const ClassTypeInfo* cls : ClassChain(obj.type)) {
    if (cls->decl != nullptr) chain.push_back({cls, of.defn_of(*cls)});
  }
  for (const ChainClass& cls : chain) {
    for (const ClassMember* member : cls.type->decl->members) {
      if (member != nullptr && member->kind == ClassMemberKind::kProperty &&
          !member->is_param) {
        CopyDeclaredClassTypespec(
            *MakePropertyVariable(made, obj, *member, ctx, build), cls.defn,
            build);
      }
    }
  }
  static const std::vector<std::string_view> kNoGenBlocks;
  std::string prefix(obj.instance);
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  RelateObjectMethods(made, chain);
  MakeObjectConstraints({made, obj, chain, of},
                        {objects, prefix, kNoGenBlocks, made, ctx}, build);
  return made;
}

VpiObject* VpiMakeSyncClassObject(uint64_t handle, std::string_view cls,
                                  const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  made->type = vpiClassObj;
  made->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kDynamic);
  made->obj_id = static_cast<int64_t>(handle);
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(cls));
  typespec->parent = made;
  made->children.push_back(typespec);
  return made;
}

void VpiRefreshSyncClassObject(
    VpiObject& obj, SimContext& ctx, const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(Process*)>& thread_of) {
  const auto kHandle = static_cast<uint64_t>(obj.obj_id);
  const MailboxObject* mbx = ctx.ContainedMailbox(kHandle);
  const void* sync = mbx != nullptr ? static_cast<const void*>(mbx)
                                    : ctx.ContainedSemaphore(kHandle);
  if (sync == nullptr) return;
  obj.children.resize(1);
  const size_t kMessages = mbx != nullptr ? mbx->messages.size() : 0;
  for (size_t index = 0; index < kMessages; ++index) {
    const Logic4Vec& held = mbx->messages[index].Get();
    VpiObject* constant = alloc();
    constant->type = vpiConstant;
    constant->const_type = MessageConstType(mbx->message_types[index]);
    Arena& arena = ctx.GetArena();
    auto* storage = arena.Create<Variable>();
    storage->value = MakeLogic4Vec(arena, held.width);
    std::copy_n(held.words, held.nwords, storage->value.words);
    storage->value.is_real = held.is_real;
    storage->value.is_signed = held.is_signed;
    storage->value.is_string = held.is_string;
    constant->var = storage;
    constant->size = static_cast<int>(held.width);
    constant->parent = &obj;
    obj.children.push_back(constant);
  }
  for (Process* proc : ctx.GetScheduler().Threads()) {
    if (proc->waiting_on_sync == sync) obj.children.push_back(thread_of(proc));
  }
}

void VpiRefreshWaitedOn(VpiObject& obj, SimContext& ctx,
                        const std::function<VpiObject*()>& alloc,
                        const std::function<VpiObject*(Process*)>& thread_of) {
  if (obj.type == vpiClassObj) {
    VpiRefreshSyncClassObject(obj, ctx, alloc, thread_of);
    return;
  }
  if (obj.type != vpiNamedEvent || obj.var == nullptr) return;
  std::erase_if(obj.children, [](const VpiObject* child) {
    return child->type == vpiThread;
  });
  for (Process* proc : ctx.GetScheduler().Threads()) {
    const auto& waits = proc->waiting_on_events;
    if (proc->active && std::ranges::find(waits, obj.var) != waits.end()) {
      obj.children.push_back(thread_of(proc));
    }
  }
}

VpiHandle VpiContext::ClassObjectOf(VpiObject& class_var) {
  if (class_var.var == nullptr || sim_ctx_ == nullptr) {
    return class_var.referenced_object;
  }
  VpiRefreshElementCopy(class_var);
  const uint64_t kHandle = class_var.var->value.ToUint64();
  if (ClassObject* obj = sim_ctx_->GetClassObject(kHandle)) {
    return MadeClassObject(*obj);
  }
  SemaphoreObject* sem = sim_ctx_->ContainedSemaphore(kHandle);
  const void* sync = sem != nullptr ? static_cast<const void*>(sem)
                                    : sim_ctx_->ContainedMailbox(kHandle);
  if (sync == nullptr) return nullptr;
  VpiObject*& made = run_objects_[sync];
  if (made == nullptr) {
    made = VpiMakeSyncClassObject(
        kHandle, sem != nullptr ? "semaphore" : "mailbox",
        {[this] { return AllocObject(); }, VpiPoolKeeper(name_pool_),
         sim_ctx_->GetArena()});
  }
  return made;
}

void VpiContext::NoteObjectReclaimed(ClassObject& obj) {
  if (sim_ctx_ == nullptr) return;
  if (!run_objects_.contains(&obj) &&
      !HasCallbackFor(callbacks_, cbReclaimObj) &&
      !HasCallbackFor(callbacks_, cbEndOfObject)) {
    return;
  }
  ReleaseClassObject(MadeClassObject(obj));
}

VpiHandle VpiContext::MadeClassObject(ClassObject& obj) {
  VpiObject*& made = run_objects_[&obj];
  if (made == nullptr || made->obj_id != static_cast<int64_t>(obj.handle)) {
    std::vector<VpiDeferredCall> deferred;
    const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                                VpiPoolKeeper(name_pool_), sim_ctx_->GetArena(),
                                &deferred};
    made = VpiMakeClassObject(
        obj,
        {[this, &obj](const ClassTypeInfo& cls) {
           return ClassDefnOf(&cls, obj.instance, object_map_, run_objects_);
         },
         [this](const VpiObject* defn) -> const VpiClassCallSite& {
           return call_objects_.class_sites[defn];
         }},
        object_map_, *sim_ctx_, kBuild);
    VpiShapeDeferredCalls(call_objects_.design, object_map_, deferred,
                          CallBuild(), kBuild);
  }
  return made;
}

}  // namespace delta
