#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Whether `obj` is a scope. §37.12 detail 1 makes an unnamed begin or fork one
// only where it directly declares a block item, and detail 2 a for statement
// only where it declares its loop variables; every other kind the scope class
// groups is one always.
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

}  // namespace

bool VpiIsInternalScopeType(int type) {
  // §37.12 (figure): `scope` is drawn as a class enclosure, which §37.4.1 makes
  // a grouping rather than an object kind, so the vpiInternalScope relation
  // drawn to it reaches the kinds it groups: the instances, tasks and
  // functions, the four block kinds, class defns, typespecs and objects,
  // clocking blocks, gen scopes, and for and foreach statements.
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

bool TryResolveStmtScopeRelation(int type, VpiHandle ref, VpiHandle& out) {
  // §37.12 and §37.63 (figures): a statement reaches the scope it stands in
  // through the untagged arrow to `scope`, the nearest object around it that
  // is one; a block that is no scope is passed over.
  if (type != vpiScope || !VpiIsScopeBodyStmtObject(ref)) return false;
  out = nullptr;
  for (VpiObject* scope = ref->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsScopeObject(scope)) {
      out = scope;
      break;
    }
  }
  return true;
}

}  // namespace delta
