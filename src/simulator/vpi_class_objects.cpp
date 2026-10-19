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
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.17 with §8.3: the kind of variable a property declared as `member` is,
// a class var where its type names a class the run knows, a package's through
// its scope by the "p::P" key the run holds it under (§26.3), and where it
// declares unpacked dimensions, a named event array for an array of events
// (§37.33 with §37.27) and an array var for any other.
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

// §37.33 detail 7: the elements of the array of virtual interfaces `var`
// stands as, each a virtual interface var of its own, named by an index of
// each dimension the array declares, so that a vpiVirtualInterfaceVar
// iteration of the class obj returns each separately.
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

// §37.33 detail 5: the class typespec the variable `var` was declared with,
// where it is a class var, as the property of its name the class defn `defn`
// holds it; nothing where the class has no defn.
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

// §37.33 detail 6 with §37.17 detail 24: the variable the property `member`
// of the object `obj` stands as, under the class obj `holder`, automatic or
// static as declared, with the indices of its fixed unpacked dimensions, the
// visibility it was declared with and a copy of the value the object holds;
// the variable is returned.
VpiObject* MakePropertyVariable(VpiObject* holder, ClassObject& obj,
                                const ClassMember& member, SimContext& ctx,
                                const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = PropertyVariableKind(member, ctx);
  VpiRecordWrittenDims(*var, member.unpacked_dims, ctx);
  var->name = build.keep(std::string(member.name));
  var->parent = holder;
  var->automatic = !member.is_static;
  // §37.3.7: a property other than a static one is part of the class object,
  // in the dynamic memory the object was allocated in.
  var->alloc_scheme = VpiAllocSchemeFor(
      member.is_static ? VpiAllocKind::kOther : VpiAllocKind::kDynamic);
  if (member.is_local) {
    var->visibility = vpiLocalVis;
  } else if (member.is_protected) {
    var->visibility = vpiProtectedVis;
  }
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

// §8.13: the class `type` and those it extends, the base first. The bound
// stops a chain of extensions that loops.
std::vector<const ClassTypeInfo*> ClassChain(const ClassTypeInfo* type) {
  constexpr int kMaxDepth = 64;
  std::vector<const ClassTypeInfo*> chain;
  for (int depth = 0; depth < kMaxDepth && type != nullptr; ++depth) {
    chain.insert(chain.begin(), type);
    type = type->parent;
  }
  return chain;
}

// §37.32 with §37.31: the class defn of the class `type`, for an object
// created in the instance `instance` names. A class a module declares has one
// under each instance of the module, and the object's is the one under the
// instance it was created in, found among the `objects` by that instance's
// path; any other class has the one `by_decl` holds for its declaration, as
// has a class of the first top.
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

// A class of a class obj's chain and the class defn it stands as, null for
// none (§37.32).
struct ChainClass {
  const ClassTypeInfo* type;
  VpiObject* defn;
};

// What a class obj's constraints are made with: the class obj `holder` of
// the object `obj`, the classes `chain` names, base first, and where each
// class's calls find their callees (`of`).
struct ObjectConstraintSite {
  VpiObject* holder;
  ClassObject& obj;
  const std::vector<ChainClass>& chain;
  const VpiClassObjDefn& of;
};

// §37.33 with §37.34: a constraint per constraint block of the classes `at`
// names, under its class obj, whose constraint_mode() state each reports
// (§18.9). A name in one resolves through `names`, and a call in one stands
// in the class obj, its callee found where the class declaring the block is
// declared (§37.42, §8.13).
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

// §37.33 detail 6 with §8.14: the methods the classes `chain` names declare,
// as their class defns made them, under the class obj `holder`; a method a
// class overrides is its override alone, the chain walked from the derived
// class. A built-in method no declaration names has no method object.
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

// §37.33 detail 8 with §37.28: the parameter `param` of the class `decl`,
// under the class obj `holder`, local where it was declared so: a type
// parameter, which has no value, or a value parameter holding the value
// `assign` binds it to, which every value parameter of a class the run holds
// has (InitClassParams in lowerer_class.cpp).
void MakeObjectParameter(VpiObject* holder, const ClassDecl& decl,
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
}

// §37.33 detail 4 with §15.4.5: the kind of constant a message is, as the
// kind of the value the mailbox placed says, a parameterized mailbox's among
// them (§15.4.9): a literal's value carries no string mark of its own.
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

}  // namespace

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
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(obj.type->name));
  typespec->parent = made;
  VpiObject* defn = of.defn_of(*obj.type);
  if (defn != nullptr) typespec->children.push_back(defn);
  made->children.push_back(typespec);
  // §37.33 detail 8: the parameters the class typespec the object was created
  // with gives values to, port list and body alike.
  const ClassTypespecInfo kTypespec = VpiClassTypespecOf(obj.type);
  for (std::size_t i = 0; i < kTypespec.params.size(); ++i) {
    MakeObjectParameter(made, *obj.type->decl, kTypespec.params[i],
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
  // A name in a constraint finds the object's variables first, then the
  // instance's or package's the object was created in, keyed in `objects`.
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
  // §37.33 detail 4 with §15.4: a message is any singular expression, held as
  // the value put() was handed.
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
  // §37.33 detail 3: a process waiting to get or put a message, or for a key.
  for (Process* proc : ctx.GetScheduler().Threads()) {
    if (proc->waiting_on_sync == sync) obj.children.push_back(thread_of(proc));
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
  // §15.3 and §15.4: a semaphore or a mailbox is an object of a built-in class
  // the run keeps by its identity, which its handle is.
  SemaphoreObject* sem = sim_ctx_->ContainedSemaphore(kHandle);
  const void* sync = sem != nullptr ? static_cast<const void*>(sem)
                                    : sim_ctx_->ContainedMailbox(kHandle);
  if (sync == nullptr) return nullptr;
  VpiObject*& made = run_objects_[sync];
  if (made == nullptr) {
    made = VpiMakeSyncClassObject(kHandle,
                                  sem != nullptr ? "semaphore" : "mailbox",
                                  {[this] { return AllocObject(); },
                                   [this](std::string name) {
                                     name_pool_.push_back(std::move(name));
                                     return std::string_view(name_pool_.back());
                                   },
                                   sim_ctx_->GetArena()});
  }
  return made;
}

void VpiContext::NoteObjectReclaimed(ClassObject& obj) {
  // §37.2.2 item 3 and §37.3.8: a class object the garbage collector reclaims
  // releases the handles to it and to its automatic members, and cbReclaimObj
  // and cbEndOfObject report the reclaim. An object no application asked for
  // has no object of the model, and is made one only where a callback is there
  // to be told of its end.
  if (sim_ctx_ == nullptr) return;
  if (!run_objects_.contains(&obj) &&
      !HasCallbackFor(callbacks_, cbReclaimObj) &&
      !HasCallbackFor(callbacks_, cbEndOfObject)) {
    return;
  }
  ReleaseClassObject(MadeClassObject(obj));
}

VpiHandle VpiContext::MadeClassObject(ClassObject& obj) {
  // §37.33 detail 1: an identifier may be reused once its object is
  // reclaimed, so an object made for one that has since gone is made afresh.
  VpiObject*& made = run_objects_[&obj];
  if (made == nullptr || made->obj_id != static_cast<int64_t>(obj.handle)) {
    // §37.42: the calls the object's constraints write, shaped once it is.
    std::vector<VpiDeferredCall> deferred;
    const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                                [this](std::string name) {
                                  name_pool_.push_back(std::move(name));
                                  return std::string_view(name_pool_.back());
                                },
                                sim_ctx_->GetArena(), &deferred};
    // A class whose defn was not made finds its callees among the
    // compilation unit's declarations alone.
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
