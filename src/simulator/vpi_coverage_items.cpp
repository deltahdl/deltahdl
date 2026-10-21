#include "simulator/vpi_coverage_items.h"

#include <optional>
#include <string>

#include "simulator/assertion_coverage.h"
#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"
#include "simulator/fsm_coverage.h"
#include "simulator/statement_coverage.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/toggle_coverage.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// vpiCovered, vpiCoveredCount and vpiCoveredMax of a handle of `kind`
// standing for `entities`; nothing for any other property.
std::optional<int> EntityProperty(int property, CoverageHandleKind kind,
                                  const EntityCoverage& entities) {
  switch (property) {
    case vpiCovered:
      return static_cast<int>(CoveredEntityCount(entities));
    case vpiCoveredCount:
      return static_cast<int>(CoveredCount(entities));
    case vpiCoveredMax:
      return static_cast<int>(CoveredMax(kind, entities));
    default:
      return std::nullopt;
  }
}

// §40.5.2 on an assertion handle. vpiCovered is true once the assertion has
// been attempted, has succeeded at least once and has never failed; it is
// covered by each nonvacuous success, or each match of a cover sequence,
// which vpiCoveredCount counts; it is one entity; and each assertion-specific
// property reads its own tally. `property` is one IsItemCoverageProperty
// accepts.
int AssertionProperty(int property, const AssertionCoverageCounters& c) {
  if (property == vpiCovered) return AssertionCovered(c) ? 1 : 0;
  if (property == vpiCoveredCount) {
    return static_cast<int>(AssertSuccessCovered(c));
  }
  if (property == vpiCoveredMax) {
    return static_cast<int>(CoveredMax(CoverageHandleKind::kAssertion, {}));
  }
  return static_cast<int>(AssertionStatusQuery(
      CoveragePropertyFromVpi(property).value_or(CoverageProperty::kCovered),
      c));
}

// §40.5.1's coverage status properties and its assertion-specific ones.
bool IsItemCoverageProperty(int property) {
  switch (property) {
    case vpiCovered:
    case vpiCoveredCount:
    case vpiCoveredMax:
    case vpiAssertAttemptCovered:
    case vpiAssertSuccessCovered:
    case vpiAssertVacuousSuccessCovered:
    case vpiAssertDisableCovered:
    case vpiAssertKillCovered:
    case vpiAssertFailureCovered:
      return true;
    default:
      return false;
  }
}

// The statement and the instance key the model's statement object `obj`
// stands for; null where it is no statement object.
const VpiStmtObjects::key_type* StatementOf(const VpiObject* obj,
                                            const VpiStmtObjects& stmts) {
  for (const auto& [key, held] : stmts) {
    if (held == obj) return &key;
  }
  return nullptr;
}

// Whether `obj` is the handle of a whole signal whose bits the run counts the
// toggles of, rather than of a bit or a part of one.
bool IsCountedSignal(const VpiObject* obj, const CodeCoverage& code) {
  return obj->var != nullptr && code.toggles.contains(obj->var) &&
         !VpiIsBitObjectType(obj->type);
}

// The hierarchical name of the instance `obj` is in; empty where it is in
// none.
std::string InstanceScopeOf(VpiObject* obj) {
  const VpiObject* inst = VpiInstanceOf(obj);
  return inst != nullptr ? inst->full_name : std::string();
}

}  // namespace

std::optional<int> VpiItemCoverage(VpiObject* obj, int property,
                                   const VpiStmtObjects& stmts,
                                   CoverageControlState& cov) {
  if (!IsItemCoverageProperty(property)) return std::nullopt;
  CodeCoverage& code = cov.Code();
  auto fsm = code.fsm_handles.find(obj);
  if (fsm != code.fsm_handles.end()) {
    return EntityProperty(property,
                          fsm->second.state ? CoverageHandleKind::kFsmState
                                            : CoverageHandleKind::kAggregate,
                          FsmHandleCoverage(fsm->second, cov));
  }
  if (VpiIsAssertionType(obj->type)) {
    return AssertionProperty(property,
                             AssertionTallies(VpiAssertionKeyOf(*obj), cov));
  }
  if (const auto* stmt = StatementOf(obj, stmts)) {
    return EntityProperty(
        property, CoverageHandleKind::kAggregate,
        StatementHandleCoverage(stmt->first, stmt->second, cov));
  }
  if (IsCountedSignal(obj, code)) {
    return EntityProperty(
        property, CoverageHandleKind::kAggregate,
        SignalToggleCoverage(obj->var, InstanceScopeOf(obj), cov));
  }
  return std::nullopt;
}

bool TryResolveFsmRelation(int type, VpiObject* ref, VpiObject*& out) {
  if (type != vpiFsmStateExpression) return false;
  const auto& handles =
      GetGlobalVpiContext().GetCoverageControlState().Code().fsm_handles;
  auto found = handles.find(ref);
  out = found != handles.end() ? found->second.state_expression : nullptr;
  return true;
}

int VpiControlAssertionCoverage(CoverageControl control, int coverage_type,
                                VpiObject& assertion,
                                CoverageControlState& cov) {
  if (coverage_type != vpiAssertCoverage) {
    return static_cast<int>(CoverageStatus::kError);
  }
  return static_cast<int>(ControlAssertionCoverage(
      control, VpiAssertionKeyOf(assertion), InstanceScopeOf(&assertion), cov));
}

}  // namespace delta
