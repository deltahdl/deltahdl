#pragma once

#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct ClassMember;
struct ClassObject;
struct ClassTypeInfo;
struct Process;

// §37.17 details 15 and 22 with §18.4 and §6.20.6: records on `var`, the
// variable the class property `member` stands as, whether it was declared
// rand, randc or neither, and whether it was declared const.
void VpiRecordPropertyDecl(VpiObject& var, const ClassMember& member);

// What a class obj is made with besides its object: the class defn each class
// of the object's chain stands as, null for none (§37.32), and where the calls
// a class defn's class's constraints write find their callees: where that
// class is declared (§37.42, §8.13).
struct VpiClassObjDefn {
  std::function<VpiObject*(const ClassTypeInfo& cls)> defn_of;
  std::function<const VpiClassCallSite&(const VpiObject* defn)> calls;
};

// §37.33 details 1, 5, 6 and 8: the class obj standing for the run's class
// object `obj`, made with `build`: its vpiObjId is the object's handle, it
// holds a class typespec of the class the object was created with, reaching
// that class's defn where there is one (§37.32); a parameter per parameter
// that class declares, holding the value its class typespec gives it; a
// variable per property that class and the classes it extends declare, base
// first, each holding a copy of the value the object holds; the methods they
// declare; and a constraint per constraint block they declare (§37.34), whose
// names resolve among the object's variables and then among `objects`, and a
// call in which stands in the class obj, its callee found where `of.calls`
// says of the class declaring the constraint (§37.42).
VpiObject* VpiMakeClassObject(ClassObject& obj, const VpiClassObjDefn& of,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

// §15.3 and §15.4 with §37.33: the class obj standing for the semaphore or
// mailbox whose handle is `handle`: an object of the built-in class `cls`
// names, a class typespec of which it holds, reaching no class defn (§37.32).
VpiObject* VpiMakeSyncClassObject(uint64_t handle, std::string_view cls,
                                  const VpiAttachBuild& build);

// §37.33 details 3 and 4: bring the class obj `obj` up to date where it stands
// for a semaphore or mailbox the run `ctx` holds - a constant per message a
// mailbox holds, in queue order, each made by `alloc`, and the thread
// `thread_of` gives for each process parked on either - after its class
// typespec; nothing for any other class obj.
void VpiRefreshSyncClassObject(
    VpiObject& obj, SimContext& ctx, const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(Process*)>& thread_of);

// The storage of the value the property `name` of `obj` holds now: a ref
// cell's where one stands (§13.5.2), the object's own, or the class's where
// the property is static (§8.9); null where none holds one.
Logic4Vec* VpiHeldPropertyValue(ClassObject& obj, std::string_view name);

// §37.42 detail 2: the member `members` name in turn, each in the class obj
// the class var before it references as `object_of` reads it, from `var` on;
// null where a link is no class var or references nothing.
template <typename ObjectOf>
VpiHandle MemberChainEnd(VpiHandle var,
                         const std::vector<std::string_view>& members,
                         const ObjectOf& object_of) {
  for (std::string_view member : members) {
    if (var == nullptr || var->type != vpiClassVar) return nullptr;
    VpiHandle obj = object_of(*var);
    if (obj == nullptr) return nullptr;
    var = ChildNamed(obj, member);
  }
  return var;
}

// §37.33 details 2 and 5: a class var references the object its value names
// now, as `object_of` reads it, which the relations through it reach; and the
// prefix of a method applied through a chain of members is read through the
// objects the chain's class vars reference now (§37.42 detail 2).
template <typename ObjectOf>
bool TryResolveRunClassRelation(int type, VpiHandle ref,
                                const ObjectOf& object_of, VpiHandle& out) {
  if (ref->type == vpiClassVar) ref->referenced_object = object_of(*ref);
  if (type != vpiPrefix || ref->prefix_members.empty()) return false;
  out = MemberChainEnd(ref->tf_prefix, ref->prefix_members, object_of);
  return true;
}

}  // namespace delta
