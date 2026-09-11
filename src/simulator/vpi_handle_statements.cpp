#include "simulator/vpi.h"
// The statement-class predicates and the for-header helper these resolvers ask
// are declared here.
#include "simulator/vpi_internal.h"

namespace delta {

// ===========================================================================
// The vpi_handle() relations of the statement model: the untagged arrow every
// statement that holds a body draws to §37.4.1's `stmt` class, §37.74's two
// single arrows to a for statement's header, and §37.63's edge from a statement
// back to the process it runs in. They sit in a file of their own because the
// resolvers they were written beside had grown past the length
// .github/workflows/deltahdl.yml admits a source file.
// ===========================================================================

// §37.63/§37.66/§37.67/§37.70/§37.71/§37.73/§37.74: the body statement the
// object model draws an untagged arrow to `stmt` for, and the two single arrows
// §37.74 draws to a for statement's header. VpiIsBodyStmtOwnerType names the
// kinds that draw the untagged arrow and says why they are one relation rather
// than six; the body itself is the first child of a kind the `stmt` class
// groups, because §37.4.1 makes that enclosure a class and no statement of a
// design carries the class's name for its own type. The header's statements are
// the for statement's alone and are held apart from its children for that same
// reason, so they are answered here beside the body they are told from.
bool TryResolveForAndBodyStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  // §37.74: the single arrows to the first statement of each part of a for
  // statement's header, drawn beside the iterations that walk all of them.
  if (ref->type == vpiFor &&
      (type == vpiForInitStmt || type == vpiForIncStmt)) {
    out = VpiForHeaderStmt(type, ref);
    return true;
  }
  if (type != vpiStmt || !VpiIsBodyStmtOwnerType(ref->type)) return false;
  for (auto* child : ref->children) {
    if (!VpiIsScopeBodyStmtType(child->type)) continue;
    out = child;
    return true;
  }
  return false;
}

bool TryResolveStmtProcessRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiProcess) return false;
  for (VpiObject* scope = ref->parent; scope != nullptr;
       scope = scope->parent) {
    if (!VpiIsProcessType(scope->type)) continue;
    out = scope;
    return true;
  }
  return false;
}

bool TryResolveProcessAndStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveForAndBodyStmtRelation(type, ref, out) ||
         TryResolveStmtProcessRelation(type, ref, out);
}

}  // namespace delta
