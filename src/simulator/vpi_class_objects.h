#pragma once

#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct ClassObject;

// §37.33 details 1, 5 and 6: the class obj standing for the run's class object
// `obj`, made with `build`: its vpiObjId is the object's handle, it holds a
// class typespec of the class the object was created with, reaching that
// class's defn `defn` where there is one (§37.32), and a variable per property
// that class and the classes it extends declare, base first, each holding a
// copy of the value the object holds; and a constraint per constraint block
// they declare (§37.34), whose names resolve among the object's variables and
// then among `objects`.
VpiObject* VpiMakeClassObject(ClassObject& obj, VpiObject* defn,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

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
