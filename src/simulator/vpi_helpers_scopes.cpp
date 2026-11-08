#include <string_view>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsScopeObject(VpiHandle obj) {
  switch (obj->type) {
    case vpiBegin:
    case vpiFork:
    case vpiFor:
      return VpiBlockScopeIsScope(obj);
    default:
      return VpiIsInternalScopeType(obj->type);
  }
}

namespace {

bool VpiIsStmtOrCaseItem(VpiHandle obj) {
  return VpiIsScopeBodyStmtObject(obj) || obj->type == vpiCaseItem;
}

bool VpiIsStmtThatIsNoScope(VpiHandle obj) {
  return VpiIsStmtOrCaseItem(obj) && !VpiIsScopeObject(obj);
}

bool IsClassTypespecRelation(const VpiObject& scope, const VpiObject& child) {
  return scope.type == vpiClassTypespec &&
         (&child == scope.children.front() || child.type == vpiClassTypespec);
}

void CollectInternalScopes(VpiHandle scope, VpiHandle iter) {
  for (VpiObject* child : scope->children) {
    if (VpiIsScopeObject(child) && !IsClassTypespecRelation(*scope, *child)) {
      iter->children.push_back(child);
    } else if (VpiIsStmtThatIsNoScope(child)) {
      CollectInternalScopes(child, iter);
    }
  }
}

bool VpiIsBlockType(int type) {
  return type == vpiBegin || type == vpiNamedBegin || type == vpiFork ||
         type == vpiNamedFork;
}

}  // namespace

bool VpiIsInternalScopeType(int type) {
  if (VpiIsTaskFuncType(type)) return true;
  switch (type) {
    case kVpiModule:
    case vpiInterface:
    case vpiProgram:
    case vpiPackage:
    case vpiNamedBegin:
    case vpiBegin:
    case vpiNamedFork:
    case vpiFork:
    case vpiClassDefn:
    case vpiClassTypespec:
    case vpiClassObj:
    case vpiClockingBlock:
    case vpiGenScope:
    case vpiFor:
    case vpiForeachStmt:
      return true;
    default:
      return false;
  }
}

static VpiHandle NearestScopeAround(VpiHandle obj) {
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsScopeObject(scope)) return scope;
  }
  return nullptr;
}

bool TryResolveStmtScopeRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiScope ||
      !(VpiIsScopeBodyStmtObject(ref) || VpiIsTfCallType(ref->type) ||
        VpiIsInternalScopeType(ref->type))) {
    return false;
  }
  out = NearestScopeAround(ref);
  return true;
}

bool TryResolveVariableScopeRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiScope || !VpiIsLoopControlVarType(ref->type)) return false;
  out = NearestScopeAround(ref);
  return true;
}

static bool CollectAssertionParts(int type, VpiHandle ref, VpiHandle iter) {
  std::vector<VpiHandle> parts;
  if (type == vpiMatchItem) {
    parts = VpiExprMatchItems(ref);
  } else if (type == vpiExpr && ref->type == vpiCasePropertyItem) {
    parts = VpiCaseItemConditions(ref);
  } else {
    return false;
  }
  for (VpiHandle part : parts) iter->children.push_back(part);
  return true;
}

bool VpiCollectNestedObjects(int type, VpiHandle ref, VpiHandle iter) {
  if (type == vpiAssertion && VpiIsInstanceType(ref->type)) {
    VpiCollectInstanceAssertions(ref, iter);
    return true;
  }
  if (type == vpiInternalScope) {
    CollectInternalScopes(ref, iter);
    return true;
  }
  if (CollectAssertionParts(type, ref, iter)) return true;
  if (VpiCollectFrameAutomatics(type, ref, iter)) return true;
  if (type != vpiStmt || !VpiIsBlockType(ref->type)) return false;
  for (VpiObject* child : ref->children) {
    if (VpiIsScopeBodyStmtObject(child)) iter->children.push_back(child);
  }
  return true;
}

VpiHandle VpiNestedScopeNamed(VpiHandle parent, std::string_view name) {
  for (VpiObject* child : parent->children) {
    const bool kNamesNoLevel =
        VpiIsStmtThatIsNoScope(child) ||
        (VpiIsStmtOrCaseItem(child) && child->name.empty());
    if (!kNamesNoLevel) continue;
    for (VpiObject* nested : child->children) {
      if (nested->name == name && VpiIsScopeObject(nested)) {
        return nested;
      }
    }
    VpiHandle deeper = VpiNestedScopeNamed(child, name);
    if (deeper != nullptr) return deeper;
  }
  return nullptr;
}

}  // namespace delta
