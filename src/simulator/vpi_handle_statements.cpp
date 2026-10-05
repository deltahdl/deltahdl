#include "simulator/vpi_user.h"
// The statement-class predicates and the for-header helper these resolvers ask
// are declared here.
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

namespace delta {

// ===========================================================================
// The vpi_handle() relations of the statement model: the untagged arrow every
// statement that holds a body draws to §37.4.1's `stmt` class, §37.74's two
// single arrows to a for statement's header, §37.63's edge from a statement
// back to the process it runs in, and the edges §37.50 draws from a concurrent
// assertion to its actions among the others. They sit in a file of their own
// because the resolvers they were written beside had grown past the length
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
  if (ref->body != nullptr) {
    out = ref->body;
    return true;
  }
  // An else action a run recorded is no body, though written alone (§16.3).
  for (auto* child : ref->children) {
    if (!VpiIsScopeBodyStmtObject(child) || child == ref->else_stmt) continue;
    out = child;
    return true;
  }
  return false;
}

bool TryResolveStmtProcessRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiProcess) return false;
  if (ref->process != nullptr) {
    out = ref->process;
    return true;
  }
  for (VpiObject* scope = ref->parent; scope != nullptr;
       scope = scope->parent) {
    if (!VpiIsProcessType(scope->type)) continue;
    out = scope;
    return true;
  }
  return false;
}

// §37.42 (figure): the arrow from a system task or function call to the user
// systf whose registration it calls, which a call of a built-in system task or
// function has none of.
bool TryResolveUserSystfRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiUserSystf ||
      (ref->type != vpiSysTaskCall && ref->type != vpiSysFuncCall)) {
    return false;
  }
  out = ref->user_systf;
  return true;
}

// §37.52: the property expression a property spec reaches by its untagged
// edge, the one child a run hangs from it. The property expr class groups
// §37.54's sequence expr, which groups the bare expressions, a net or a
// variable a name stands for among them (§37.58).
static VpiHandle PropertySpecExpr(VpiHandle spec) {
  for (auto* child : spec->children) {
    if (VpiIsPropertyExprType(child->type) ||
        VpiIsSequenceExprType(child->type) || VpiIsOperandObject(child)) {
      return child;
    }
  }
  return nullptr;
}

// §37.51: the edges a property inst draws to its declaration and its disable
// condition, and the one a prop formal decl draws to its default value.
static bool TryResolvePropertyDeclRelation(int type, VpiHandle ref,
                                           VpiHandle& out) {
  if (ref->type == vpiPropFormalDecl) {
    if (type != vpiExpr) return false;
    out = VpiPropFormalInitExpr(ref);
    return true;
  }
  if (type == vpiPropertyDecl) {
    out = VpiPropertyInstDecl(ref);
    return true;
  }
  if (type != vpiDisableCondition) return false;
  out = ref->disable_condition;
  return true;
}

// §37.50: the edges a concurrent assertion draws to its clock, its property
// and its actions; §37.52: those a property spec draws to its disable
// condition and its property expression. Each is a relation tag no object
// carries for its own type, so the traversal they fell through to reached
// none of them.
static bool TryResolveAssertionRelation(int type, VpiHandle ref,
                                        VpiHandle& out) {
  if (VpiIsConcurrentAssertionType(ref->type)) {
    switch (type) {
      case vpiClockingEvent:
        out = VpiConcurrentAssertionClockingEvent(ref);
        return true;
      case vpiProperty:
        out = VpiConcurrentAssertionProperty(ref);
        return true;
      case vpiStmt:
        out = VpiConcurrentAssertionStmt(ref);
        return true;
      case vpiElseStmt:
        out = VpiConcurrentAssertionElseStmt(ref);
        return true;
      default:
        return false;
    }
  }
  if (ref->type == vpiPropertyInst || ref->type == vpiPropFormalDecl) {
    return TryResolvePropertyDeclRelation(type, ref, out);
  }
  // §37.52: a clocked property reaches the property it clocks, and a case
  // property item the property it branches to, held apart from its
  // conditions.
  if (type == vpiPropertyExpr && ref->type == vpiClockedProp) {
    out = PropertySpecExpr(ref);
    return true;
  }
  // §37.56: a clocked seq reaches the sequence expr its run of operands is.
  // Annex M names no type for the sequence expr class, so the tagless edge is
  // read with the type of the object it reaches.
  if (ref->type == vpiClockedSeq) {
    VpiHandle held = PropertySpecExpr(ref);
    if (held == nullptr || held->type != type) return false;
    out = held;
    return true;
  }
  if (type == vpiPropertyExpr && ref->type == vpiCasePropertyItem) {
    out = ref->body;
    return true;
  }
  if (ref->type != vpiPropertySpec) return false;
  if (type == vpiDisableCondition) {
    out = ref->disable_condition;
    return true;
  }
  if (type != vpiPropertyExpr) return false;
  out = PropertySpecExpr(ref);
  return true;
}

bool TryResolveProcessAndStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveAssertionRelation(type, ref, out) ||
         TryResolveForAndBodyStmtRelation(type, ref, out) ||
         TryResolveStmtProcessRelation(type, ref, out) ||
         TryResolveUserSystfRelation(type, ref, out);
}

}  // namespace delta
