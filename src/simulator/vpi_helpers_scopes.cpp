#include <string_view>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

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

namespace {

// Whether `obj` is a statement, or a case item (§37.72), which holds one.
bool VpiIsStmtOrCaseItem(VpiHandle obj) {
  return obj != nullptr &&
         (VpiIsScopeBodyStmtObject(obj) || obj->type == vpiCaseItem);
}

// Whether `obj` is a statement that is no scope: an unnamed begin or fork
// declaring nothing (§37.12 detail 1), or any other statement but a foreach
// loop or a for loop declaring its variables (detail 2). It stands between the
// scope around it and the scopes written inside it without being one they are
// nested in.
bool VpiIsStmtThatIsNoScope(VpiHandle obj) {
  return VpiIsStmtOrCaseItem(obj) && !VpiIsScopeObject(obj);
}

// §37.12 (figure): the scopes `scope` holds, reached through vpiInternalScope:
// each child that is a scope, and the scopes nested in a child statement that
// is none, which stands in the scope without nesting them in a scope of its
// own.
void CollectInternalScopes(VpiHandle scope, VpiHandle iter) {
  for (VpiObject* child : scope->children) {
    if (child == nullptr) continue;
    if (VpiIsScopeObject(child)) {
      iter->children.push_back(child);
    } else if (VpiIsStmtThatIsNoScope(child)) {
      CollectInternalScopes(child, iter);
    }
  }
}

// §37.12 (figure): begin, named begin, fork and named fork each reach the
// statements they hold, through the one-to-many arrow to the `stmt` class.
bool VpiIsBlockType(int type) {
  return type == vpiBegin || type == vpiNamedBegin || type == vpiFork ||
         type == vpiNamedFork;
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

bool VpiCollectNestedObjects(int type, VpiHandle ref, VpiHandle iter) {
  if (type == vpiAssertion && VpiIsInstanceType(ref->type)) {
    VpiCollectInstanceAssertions(ref, iter);
    return true;
  }
  if (type == vpiInternalScope) {
    CollectInternalScopes(ref, iter);
    return true;
  }
  // The `stmt` class §37.60 fills is a grouping (§37.4.1), so the iteration
  // reaches the statements the block holds, each of the kind it is, in the
  // order written, and none of the block's variables.
  if (type != vpiStmt || !VpiIsBlockType(ref->type)) return false;
  for (VpiObject* child : ref->children) {
    if (child != nullptr && VpiIsScopeBodyStmtObject(child)) {
      iter->children.push_back(child);
    }
  }
  return true;
}

VpiHandle VpiNestedScopeNamed(VpiHandle parent, std::string_view name) {
  for (VpiObject* child : parent->children) {
    // A loop that is a scope but has no name, such as a for loop declaring
    // its variables, adds no level to a name either.
    const bool kNamesNoLevel =
        VpiIsStmtThatIsNoScope(child) ||
        (VpiIsStmtOrCaseItem(child) && child->name.empty());
    if (!kNamesNoLevel) continue;
    for (VpiObject* nested : child->children) {
      if (nested != nullptr && nested->name == name &&
          VpiIsScopeObject(nested)) {
        return nested;
      }
    }
    VpiHandle deeper = VpiNestedScopeNamed(child, name);
    if (deeper != nullptr) return deeper;
  }
  return nullptr;
}

}  // namespace delta
