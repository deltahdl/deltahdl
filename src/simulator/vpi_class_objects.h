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
struct ClassDecl;
struct ClassMember;
struct ClassObject;
struct ClassTypeInfo;
struct ClassTypespecParam;
struct ClassTypespecParamAssign;
struct Process;

void VpiRecordPropertyDecl(VpiObject& var, const ClassMember& member);

struct VpiClassObjDefn {
  std::function<VpiObject*(const ClassTypeInfo& cls)> defn_of;
  std::function<const VpiClassCallSite&(const VpiObject* defn)> calls;
};

VpiObject* VpiMakeObjectParameter(VpiObject* holder, const ClassDecl& decl,
                                  const ClassTypespecParam& param,
                                  const ClassTypespecParamAssign& assign,
                                  const VpiAttachBuild& build);

VpiObject* VpiMakeClassObject(ClassObject& obj, const VpiClassObjDefn& of,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

VpiObject* VpiMakeSyncClassObject(uint64_t handle, std::string_view cls,
                                  const VpiAttachBuild& build);

void VpiRefreshSyncClassObject(
    VpiObject& obj, SimContext& ctx, const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(Process*)>& thread_of);

void VpiRefreshWaitedOn(VpiObject& obj, SimContext& ctx,
                        const std::function<VpiObject*()>& alloc,
                        const std::function<VpiObject*(Process*)>& thread_of);

Logic4Vec* VpiHeldPropertyValue(ClassObject& obj, std::string_view name);

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

template <typename ObjectOf>
bool TryResolveRunClassRelation(int type, VpiHandle ref,
                                const ObjectOf& object_of, VpiHandle& out) {
  if (ref->type == vpiClassVar) ref->referenced_object = object_of(*ref);
  if (type != vpiPrefix || ref->prefix_members.empty()) return false;
  out = MemberChainEnd(ref->tf_prefix, ref->prefix_members, object_of);
  return true;
}

}  // namespace delta
