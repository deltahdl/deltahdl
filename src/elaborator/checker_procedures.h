#ifndef DELTA_ELABORATOR_CHECKER_PROCEDURES_H
#define DELTA_ELABORATOR_CHECKER_PROCEDURES_H

#include <cstdint>

namespace delta {

enum class ProceduralBlockKind : uint8_t {
  kInitial,
  kFinal,
  kAlways,
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFf,
};

bool ProceduralBlockAllowedInChecker(ProceduralBlockKind kind);

enum class CheckerInitialContent : uint8_t {
  kLetDeclaration,
  kImmediateAssertion,
  kDeferredAssertion,
  kConcurrentAssertion,
  kEventTimingControl,
  kDelayTimingControl,
  kWaitTimingControl,
};

bool CheckerInitialProcedureAllows(CheckerInitialContent content);

enum class CheckerAlwaysForm : uint8_t {
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFf,
};

enum class CheckerAlwaysStatement : uint8_t {
  kBlockingAssignment,
  kNonblockingAssignment,
  kSelectionStatement,
  kLoopStatement,
  kTimingEventControl,
  kSubroutineCall,
  kImmediateAssertion,
  kDeferredAssertion,
  kConcurrentAssertion,
  kLetDeclaration,
};

bool CheckerAlwaysStatementAllowed(CheckerAlwaysStatement stmt,
                                   CheckerAlwaysForm form);

enum class CheckerAlwaysExpressionPosition : uint8_t {
  kEventControl,
  kBody,
};

bool CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm form,
                                      CheckerAlwaysExpressionPosition position);

bool CheckerProcedureClockInferenceFollowsProceduralAssertionRules();

bool CheckerFinalProcedureIsAllowed();

bool CheckerFinalProcedureRunsOncePerInstantiation();

bool CheckerFinalProceduresHaveImpliedOrdering();

bool CheckerFinalProcedureDependsOnInstantiationContext();

bool CheckerFinalProcedureAllowsConstruct(bool allowed_in_non_checker_final);

}  // namespace delta

#endif
