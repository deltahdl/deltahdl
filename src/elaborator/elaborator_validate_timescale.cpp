#include <cstddef>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

// §3.14: a design element's time precision shall be at least as precise as its
// time unit. When the two are written as separate timeunit/timeprecision
// statements (rather than the "unit / precision" slash form the parser already
// checks), the comparison can only happen once both have been collected, so it
// lands here. The rule is stated once and applies to every design element, so
// the per-element field comparison is shared.
// §3.14: the timescale a design element declares -- whether it states a time
// unit and a time precision, and the unit-with-magnitude each is written as.
struct DeclaredTimescale {
  bool has_unit;
  bool has_precision;
  TimeUnit unit;
  int unit_magnitude;
  TimeUnit precision;
  int precision_magnitude;
};

static void CheckTimescaleOrder(const DeclaredTimescale& ts, SourceLoc loc,
                                DiagEngine& diag) {
  if (!ts.has_unit || !ts.has_precision) return;
  if (EffectiveTimeOrder(ts.precision, ts.precision_magnitude) >
      EffectiveTimeOrder(ts.unit, ts.unit_magnitude)) {
    diag.Error(loc, "time precision is less precise than the time unit",
               Subclause("3.14"));
  }
}

static void CheckModuleTimescaleOrder(const ModuleDecl* decl,
                                      DiagEngine& diag) {
  CheckTimescaleOrder(
      {decl->has_timeunit, decl->has_timeprecision, decl->time_unit,
       decl->time_unit_magnitude, decl->time_prec, decl->time_prec_magnitude},
      decl->range.start, diag);
}

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl,
                                           RtlirModule* mod) {
  // §11.2.1: constant-expression checks below (indexed part-select width, etc.)
  // may reference module parameters, so evaluate them in the module's parameter
  // scope rather than an empty one.
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  // §11.4.12.1: expose the resolved module parameter scope to the replication-
  // multiplier checks below so a parameter-valued multiplier is const-folded
  // the same way a literal one is.
  replicate_multiplier_scope_ = scope;
  // §11.4.14.2: expose the same resolved parameter scope to the streaming
  // slice_size check so a parameter/localparam-valued slice size is
  // const-folded (and its zero/negative rejection applied) the same way a
  // literal one is.
  streaming_slice_size_scope_ = scope;
  // §20.7.1: the array-query dimension index n is a constant expression, so
  // expose the same resolved parameter scope to the variable-sized-dimension
  // check for const-folding a parameter/localparam/genvar-valued n.
  array_query_dim_scope_ = scope;
  // §20.16.3: the PLA ascending-order check folds declaration range bounds,
  // which may be parameter- or localparam-valued, so give it the same resolved
  // scope.
  pla_ascending_scope_ = scope;
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item, scope);
  }
  // The bulk of module-level validation is an ordered series of independent
  // single-element checks. Two of them inspect elaborator-wide state rather
  // than the module declaration and must run in their original positions, so
  // the dispatch is driven by an ordered table of pointer-to-member checks; a
  // null decl-check entry is the cursor for the next no-argument check. This
  // keeps the dispatch (and its exact execution order) in one place while
  // staying well under the per-function statement budget.
  using DeclCheck = void (Elaborator::*)(const ModuleDecl*);
  using PlainCheck = void (Elaborator::*)();
  static constexpr DeclCheck kDeclChecks[] = {
      &Elaborator::ValidatePackageImportRules,
      &Elaborator::ValidateScopeRules,
      nullptr,  // ValidateMixedAssignments
      &Elaborator::ValidateInputPortAssignments,
      &Elaborator::ValidateMatchesPatternIntegral,
      &Elaborator::ValidateMatchesCaseSelectorType,
      &Elaborator::ValidateMatchesIfPredicateType,
      &Elaborator::ValidateDisableTargets,
      nullptr,  // ValidateProceduralNetAssign
      &Elaborator::AdoptProceduralTypedefDims,
      &Elaborator::ValidateDynamicArrayNba,
      &Elaborator::ValidateArrayQueryOnDynamicType,
      &Elaborator::ValidateArrayQueryOnVariableDim,
      &Elaborator::ValidateRandomSeedType,
      &Elaborator::ValidatePlaOutputTerms,
      &Elaborator::ValidateStringOutputTaskTargets,
      &Elaborator::ValidatePlaAscendingOrder,
      &Elaborator::ValidateBitsCallRestrictions,
      &Elaborator::ValidateBitVectorFunctionArgs,
      &Elaborator::ValidateAutomaticVarProcWrites,
      &Elaborator::ValidateJumpStatements,
      &Elaborator::ValidateRandsequenceProductionNames,
      &Elaborator::ValidateForeachLoops,
      &Elaborator::ValidateContAssignConstSelect,
      &Elaborator::ValidatePartSelectBounds,
      &Elaborator::ValidateSpecparamInParams,
      &Elaborator::ValidateSpecparamInDeclRange,
      &Elaborator::ValidateEnumAssignments,
      &Elaborator::ValidateConstAssignments,
      &Elaborator::ValidateArrayAssignments,
      &Elaborator::ValidateAssocArraySlices,
      &Elaborator::ValidateAssocWildcardTraversal,
      &Elaborator::ValidateAssocTraversalArgType,
      &Elaborator::ValidateArrayOrderingMethods,
      &Elaborator::ValidateClassIndexSelect,
      &Elaborator::ValidateStringIndexSelect,
      &Elaborator::ValidateIntegralIndexSelect,
      &Elaborator::ValidateAssocConcatTarget,
      &Elaborator::ValidateAssocOperandInExpr,
      &Elaborator::ValidateArrayPatternElemType,
      &Elaborator::ValidateReplicateTargetingArray,
      &Elaborator::ValidateArrayElementPartSelect,
      &Elaborator::ValidateUnpackedArrayConcatNesting,
      &Elaborator::ValidateClassHandleOps,
      &Elaborator::ValidateChandleOps,
      &Elaborator::ValidateVirtualInterfaceOps,
      &Elaborator::ValidateEventOps,
      &Elaborator::ValidateVirtualInterfaceClocking,
      &Elaborator::ValidateInterfaceObjectAccess,
      &Elaborator::ValidateDeferredAssertionActions,
      &Elaborator::ValidateAggregateComparisons,
      &Elaborator::ValidateTypeRefComparisons,
      &Elaborator::ValidateTypeRefArgs,
      &Elaborator::ValidateGetpatternUses,
      &Elaborator::ValidateTaggedUnionMembers,
      &Elaborator::ValidateRealOperatorRestrictions,
      &Elaborator::ValidateCastOperations,
      &Elaborator::ValidateAssignInExprRestrictions,
      &Elaborator::ValidateUnsizedInConcat,
      &Elaborator::ValidateSelectOnConcatLvalue,
      &Elaborator::ValidateReplicateLvalue,
      &Elaborator::ValidateStringConcatLvalue,
      &Elaborator::ValidateReplicateMultiplier,
      &Elaborator::ValidateStreamingConcatContext,
      &Elaborator::ValidateBitStreamCast,
      &Elaborator::ValidateSubroutineCallArgs,
      &Elaborator::ValidateArrayArgTypes,
      &Elaborator::ValidateLocalProtectedAccess,
      &Elaborator::ValidateParameterizedScopeResolution,
      &Elaborator::ValidateRestrictedScopePrefixUsage,
      &Elaborator::ValidateTypeParamScopePrefixResolvesToClass,
      &Elaborator::ValidateStaticMethodBodies,
      &Elaborator::ValidateClassMethodBodies,
      &Elaborator::ValidateThisUsage,
  };
  // No-argument checks, consumed in order at each null table entry.
  static constexpr PlainCheck kPlainChecks[] = {
      &Elaborator::ValidateMixedAssignments,
      &Elaborator::ValidateProceduralNetAssign,
  };
  size_t plain_idx = 0;
  for (DeclCheck check : kDeclChecks) {
    if (check) {
      (this->*check)(decl);
    } else {
      (this->*kPlainChecks[plain_idx++])();
    }
  }
  CheckModuleTimescaleOrder(decl, diag_);
}

namespace {

// State for the §3.14.2.3 timescale-consistency scan: the compilation-unit
// fallback timescale (used when a design element omits its own) plus the
// running record of whether any element was fully specified or unspecified.
struct TimescaleScan {
  bool cu_fallback_unit = false;
  bool cu_fallback_prec = false;
  bool any_specified = false;
  bool any_unspecified = false;
  SourceLoc unspecified_loc;
};

void ClassifyTimescaleElement(bool el_has_unit, bool el_has_prec, SourceLoc loc,
                              TimescaleScan& scan) {
  bool has_unit = el_has_unit || scan.cu_fallback_unit;
  bool has_prec = el_has_prec || scan.cu_fallback_prec;
  if (has_unit && has_prec) {
    scan.any_specified = true;
  } else {
    if (!scan.any_unspecified) scan.unspecified_loc = loc;
    scan.any_unspecified = true;
  }
}

}  // namespace

void Elaborator::ValidateTimescaleConsistency() {
  TimescaleScan scan;
  scan.cu_fallback_unit =
      unit_->has_preproc_timescale || unit_->has_cu_timeunit;
  scan.cu_fallback_prec =
      unit_->has_preproc_timescale || unit_->has_cu_timeprecision;
  auto inspect = [&](bool el_has_unit, bool el_has_prec, SourceLoc loc) {
    ClassifyTimescaleElement(el_has_unit, el_has_prec, loc, scan);
  };

  for (const auto* mod : unit_->modules)
    inspect(mod->has_timeunit, mod->has_timeprecision, mod->range.start);
  for (const auto* iface : unit_->interfaces)
    inspect(iface->has_timeunit, iface->has_timeprecision, iface->range.start);
  for (const auto* prog : unit_->programs)
    inspect(prog->has_timeunit, prog->has_timeprecision, prog->range.start);

  if (scan.any_specified && scan.any_unspecified) {
    diag_.Error(scan.unspecified_loc,
                "some design elements specify time unit and precision while "
                "others do not",
                Subclause("3.14.2.3"));
  }
}

// §3.14: enforce the precision-no-coarser-than-unit rule for the design
// elements that are not necessarily reached through module item elaboration.
// A package is never elaborated that way, and an interface or program that is
// declared but never instantiated is likewise skipped, so the
// separate-statement form of the check that CheckModuleTimescaleOrder performs
// for modules would otherwise never run for them. Scanning the declarations
// directly (as the consistency check in ValidateTimescaleConsistency already
// does) covers every such element exactly once.
void Elaborator::ValidateStandaloneTimescaleOrder() {
  auto check = [&](const ModuleDecl* decl) {
    CheckModuleTimescaleOrder(decl, diag_);
  };
  for (const auto* iface : unit_->interfaces) check(iface);
  for (const auto* prog : unit_->programs) check(prog);
  for (const auto* pkg : unit_->packages) {
    CheckTimescaleOrder(
        {pkg->has_timeunit, pkg->has_timeprecision, pkg->time_unit,
         pkg->time_unit_magnitude, pkg->time_prec, pkg->time_prec_magnitude},
        pkg->range.start, diag_);
  }
}

}  // namespace delta
