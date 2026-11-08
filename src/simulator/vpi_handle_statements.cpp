#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool TryResolveForAndBodyStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
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

bool TryResolveUserSystfRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiUserSystf ||
      (ref->type != vpiSysTaskCall && ref->type != vpiSysFuncCall)) {
    return false;
  }
  out = ref->user_systf;
  return true;
}

static VpiHandle PropertySpecExpr(VpiHandle spec) {
  for (auto* child : spec->children) {
    if (VpiIsPropertyExprType(child->type) ||
        VpiIsSequenceExprType(child->type) || VpiIsOperandObject(child)) {
      return child;
    }
  }
  return nullptr;
}

static bool TryResolveSequenceDeclRelation(int type, VpiHandle ref,
                                           VpiHandle& out) {
  if (ref->type != vpiSequenceInst && ref->type != vpiSequenceDecl &&
      ref->type != vpiSeqFormalDecl && ref->type != vpiLetDecl) {
    return false;
  }
  if (ref->type == vpiSequenceInst) {
    if (type != vpiSequenceDecl) return false;
    out = VpiSequenceInstDecl(ref);
    return true;
  }
  if (type != vpiExpr) return false;
  out = ref->type == vpiSequenceDecl ? VpiSeqDeclBodyExpr(ref)
                                     : VpiSeqFormalInitExpr(ref);
  return true;
}

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

static bool TryResolveClockedSeqRelation(int type, VpiHandle ref,
                                         VpiHandle& out) {
  if (ref->type != vpiClockedSeq) return false;
  VpiHandle held = PropertySpecExpr(ref);
  if (held == nullptr || held->type != type) return false;
  out = held;
  return true;
}

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
  if (type == vpiPropertyExpr && ref->type == vpiClockedProp) {
    out = PropertySpecExpr(ref);
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
         TryResolveSequenceDeclRelation(type, ref, out) ||
         TryResolveClockedSeqRelation(type, ref, out) ||
         TryResolveForAndBodyStmtRelation(type, ref, out) ||
         TryResolveStmtProcessRelation(type, ref, out) ||
         VpiTryResolveThreadRelation(type, ref, out) ||
         VpiTryResolveFrameRelation(type, ref, out) ||
         TryResolveUserSystfRelation(type, ref, out);
}

}  // namespace delta
