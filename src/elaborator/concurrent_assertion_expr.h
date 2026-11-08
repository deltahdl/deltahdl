#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

struct CompilationUnit;
struct Expr;
struct RtlirModule;

enum class AssertionBooleanExprPlace : uint8_t {
  kSequenceOrPropertyExpr,
  kClockingEvent,
  kDisableCondition,
};

bool ConcurrentAssertionExprTypeIsAcceptable(bool overall_result_castable);
bool ConcurrentAssertionSubexprTypeIsExempt();

bool AutomaticVariableReferenceAllowed(
    bool inside_procedural_concurrent_assertion);

bool NonStaticClassMemberReferenceAllowed();

std::string ConcurrentAssertionExprReferencedNonStaticMember(
    const Expr* body, const RtlirModule* mod, const CompilationUnit* unit);

bool ChandleVariableReferenceAllowed();

std::string_view ConcurrentAssertionExprReferencedChandle(
    const Expr* body, const RtlirModule* mod);

bool SideEffectAllowed(bool inside_sequence_match_item,
                       bool variable_lvalue_is_local);

enum class FunctionArgKind : uint8_t {
  kInput,
  kOutput,
  kInout,
  kRef,
  kConstRef,
};
bool FunctionArgKindAllowedInAssertionExpr(FunctionArgKind kind);

bool FunctionEligibleInAssertionExpr(bool is_automatic, bool preserves_no_state,
                                     bool has_no_side_effects);

enum class DisableConditionRefKind : uint8_t {
  kOrdinaryVariable,
  kLocalVariable,
  kTriggeredMethod,
  kMatchedMethod,
};
bool DisableConditionRefAllowed(DisableConditionRefKind kind);

}  // namespace delta
