#include <cstddef>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/class_property_cont_assign.h"
#include "elaborator/const_eval.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/instance_local_types.h"
#include "elaborator/rtlir.h"
#include "elaborator/unit_scope_switch.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

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
  // §7.7: the array-argument check folds a formal's dimension bounds, which may
  // be parameter-valued, in the same scope.
  array_arg_dim_scope_ = scope;
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
      &Elaborator::ValidateAggregateOperands,
      &Elaborator::ValidateArrayPatternElemType,
      &Elaborator::ValidateProceduralArrayPatterns,
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
      &Elaborator::ValidateLetScope,
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
      &Elaborator::ValidateConstPropertyWritesFromOutside,
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
  CheckIsunboundedArgs(decl, diag_);
  std::unordered_set<std::string_view> unbounded;
  for (const auto& param : mod->params) {
    if (param.is_unbounded) unbounded.insert(param.name);
  }
  std::unordered_set<std::string_view> queues;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_queue) queues.insert(name);
  }
  CheckUnboundedParamsInQueueContexts(decl, unbounded, queues, diag_);
  CheckDollarOperands(decl, diag_);
  CheckContinuousPropertyWrites(decl, class_var_types_, unit_, diag_);
  CheckInstanceLocalTypeAssignments(decl, unit_, diag_);
}

namespace {

// One half of what a time scope declares (§3.14.2.2): whether it states the
// time unit, or the time precision, and the unit-with-magnitude it is written
// as.
struct DeclaredTime {
  bool declared;
  TimeUnit unit;
  int magnitude;
};

struct DeclaredTimescale {
  DeclaredTime unit;
  DeclaredTime precision;
};

DeclaredTimescale DeclaredBy(const ModuleDecl* decl) {
  return {
      {decl->has_timeunit, decl->time_unit, decl->time_unit_magnitude},
      {decl->has_timeprecision, decl->time_prec, decl->time_prec_magnitude}};
}

DeclaredTimescale DeclaredBy(const PackageDecl* pkg) {
  return {{pkg->has_timeunit, pkg->time_unit, pkg->time_unit_magnitude},
          {pkg->has_timeprecision, pkg->time_prec, pkg->time_prec_magnitude}};
}

DeclaredTimescale DeclaredBy(const CompilationUnit* cu) {
  return {
      {cu->has_cu_timeunit, cu->cu_time_unit, cu->cu_time_unit_magnitude},
      {cu->has_cu_timeprecision, cu->cu_time_prec, cu->cu_time_prec_magnitude}};
}

// A `timescale directive (§22.7) states both halves or, absent, neither.
DeclaredTimescale DeclaredBy(bool has_timescale, const TimeScale& ts) {
  return {{has_timescale, ts.unit, ts.magnitude},
          {has_timescale, ts.precision, ts.prec_magnitude}};
}

// The running record of the §3.14.2.3 timescale-consistency scan: whether any
// element was fully specified, whether any was not, and where the first that
// was not stands.
struct TimescaleScan {
  bool any_specified = false;
  bool any_unspecified = false;
  SourceLoc unspecified_loc;
};

// An element specifies its time unit, and likewise its precision, when it
// declares it, when a `timescale precedes its header (§3.14.2.3 b), or when
// the compilation unit declares one (c). Only the default (d) leaves it
// unspecified.
void ClassifyTimescaleElement(const DeclaredTimescale& own,
                              const DeclaredTimescale& directive,
                              const DeclaredTimescale& cu, SourceLoc loc,
                              TimescaleScan& scan) {
  bool has_unit =
      own.unit.declared || directive.unit.declared || cu.unit.declared;
  bool has_prec = own.precision.declared || directive.precision.declared ||
                  cu.precision.declared;
  if (has_unit && has_prec) {
    scan.any_specified = true;
  } else {
    if (!scan.any_unspecified) scan.unspecified_loc = loc;
    scan.any_unspecified = true;
  }
}

// A design element's time unit or time precision as §3.14.2.3 (printed page
// 60) resolves it, and whether it came from the module or interface enclosing
// the element. The default is the 1 ns deltahdl takes for both, which §3.14.2.3
// leaves to the implementation and the TimeScale struct starts from.
struct ResolvedTime {
  TimeUnit unit = TimeUnit::kNs;
  int magnitude = 1;
  bool inherited = false;
};

struct ElementTimescale {
  ResolvedTime unit;
  ResolvedTime precision;
};

// §3.14.2.3: an element takes each of the two from its own declaration, else
// from the module or interface enclosing it (a), else from the `timescale in
// force at its header (b), else from the compilation unit's declaration (c),
// and otherwise from the default (d). A precision the element does not declare
// is found by the same order of sources as a unit.
ResolvedTime ResolveTime(const DeclaredTime& own, const ResolvedTime* enclosing,
                         const DeclaredTime& directive,
                         const DeclaredTime& cu) {
  if (own.declared) return {own.unit, own.magnitude, false};
  if (enclosing != nullptr)
    return {enclosing->unit, enclosing->magnitude, true};
  if (directive.declared) return {directive.unit, directive.magnitude, false};
  if (cu.declared) return {cu.unit, cu.magnitude, false};
  return {};
}

ElementTimescale ResolveElementTimescale(const DeclaredTimescale& own,
                                         const ElementTimescale* enclosing,
                                         const DeclaredTimescale& directive,
                                         const DeclaredTimescale& cu) {
  return {
      ResolveTime(own.unit, enclosing ? &enclosing->unit : nullptr,
                  directive.unit, cu.unit),
      ResolveTime(own.precision, enclosing ? &enclosing->precision : nullptr,
                  directive.precision, cu.precision)};
}

// §3.14 (printed page 59): a design element's time precision may be no coarser
// than its time unit. The comparison is of the two values the element resolves
// to, wherever each came from, so a lone `timeunit 1ps;` is held to the 1 ns
// default precision. A pair a nested element inherits whole from the one
// enclosing it is that element's pair, reported there. An extern declaration
// (§23.5) is not an element of its own and is left to its definition.
void CheckTimescaleOrder(const ElementTimescale& ts, SourceLoc loc,
                         DiagEngine& diag) {
  if (ts.unit.inherited && ts.precision.inherited) return;
  if (EffectiveTimeOrder(ts.precision.unit, ts.precision.magnitude) >
      EffectiveTimeOrder(ts.unit.unit, ts.unit.magnitude)) {
    diag.Error(loc, "time precision is less precise than the time unit",
               Subclause("3.14"));
  }
}

// Checks a module, interface or program and every module or interface nested
// in it, each nested one resolving against the element enclosing it.
void CheckDesignElementTimescales(const ModuleDecl* decl,
                                  const ElementTimescale* enclosing,
                                  const DeclaredTimescale& cu,
                                  DiagEngine& diag) {
  if (decl->is_extern) return;
  ElementTimescale ts = ResolveElementTimescale(
      DeclaredBy(decl), enclosing,
      DeclaredBy(decl->has_directive_timescale, decl->directive_timescale), cu);
  CheckTimescaleOrder(ts, decl->range.start, diag);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl) {
      CheckDesignElementTimescales(item->nested_module_decl, &ts, cu, diag);
    }
  }
}

}  // namespace

// The design elements `unit` declares, each classified into `scan` against
// `unit`'s own compilation-unit declarations.
static void ScanTimescaleElements(const CompilationUnit* unit,
                                  TimescaleScan& scan) {
  DeclaredTimescale cu = DeclaredBy(unit);

  // An extern declaration (§23.5) declares the ports of the design element its
  // definition gives, and is not an element of its own, so only the definition
  // is classified.
  for (const auto* list :
       {&unit->modules, &unit->interfaces, &unit->programs}) {
    for (const auto* decl : *list) {
      if (decl->is_extern) continue;
      ClassifyTimescaleElement(
          DeclaredBy(decl),
          DeclaredBy(decl->has_directive_timescale, decl->directive_timescale),
          cu, decl->range.start, scan);
    }
  }
  // §3.2 (printed page 50) counts a package among the design elements, and
  // §3.14.2.2 lets it declare its own time unit and precision.
  for (const auto* pkg : unit->packages) {
    ClassifyTimescaleElement(
        DeclaredBy(pkg),
        DeclaredBy(pkg->has_directive_timescale, pkg->directive_timescale), cu,
        pkg->range.start, scan);
  }
}

void Elaborator::ValidateTimescaleConsistency() {
  TimescaleScan scan;
  // §3.14.2.3 (printed page 60) states the rule over the design elements of
  // the design, whichever compilation unit each stands in, and §3.12.1 gives
  // each its own unit's declarations to be specified by.
  UnitScopeTables::ForEachUnit(*this,
                               [&] { ScanTimescaleElements(unit_, scan); });

  if (scan.any_specified && scan.any_unspecified) {
    diag_.Error(scan.unspecified_loc,
                "some design elements specify time unit and precision while "
                "others do not",
                Subclause("3.14.2.3"));
  }
}

// §3.14: enforce the precision-no-coarser-than-unit rule on every design
// element that can carry a time unit, from its declaration rather than from
// module item elaboration: a package is never elaborated that way, and a
// module, interface or program that is declared but never instantiated is
// skipped by it, so scanning the declarations covers each exactly once. A
// package is never nested, so it resolves from its own declarations, the
// `timescale before its header and the compilation unit alone.
void Elaborator::ValidateTimescaleOrder() {
  DeclaredTimescale cu = DeclaredBy(unit_);
  for (const auto* list :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (const auto* decl : *list) {
      CheckDesignElementTimescales(decl, nullptr, cu, diag_);
    }
  }
  for (const auto* pkg : unit_->packages) {
    CheckTimescaleOrder(
        ResolveElementTimescale(
            DeclaredBy(pkg), nullptr,
            DeclaredBy(pkg->has_directive_timescale, pkg->directive_timescale),
            cu),
        pkg->range.start, diag_);
  }
}

}  // namespace delta
