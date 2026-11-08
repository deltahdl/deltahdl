#include <cstddef>
#include <functional>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/class_property_cont_assign.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/declared_types.h"
#include "elaborator/default_pattern_values.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/instance_local_types.h"
#include "elaborator/net_data_type.h"
#include "elaborator/nettype_uses.h"
#include "elaborator/new_placement.h"
#include "elaborator/rtlir.h"
#include "elaborator/time_literal_scale.h"
#include "elaborator/unit_scope_switch.h"
#include "elaborator/unpacked_dim_reads.h"
#include "elaborator/virtual_interface_target.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

void CheckInnerDeclaredTypes(
    const ModuleDecl* decl, const AggregateShapeCtx& ctx,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    const std::function<bool(std::string_view)>& names_covergroup) {
  ForEachInnerDeclaredType(decl, [&](const DeclaredType& declared) {
    CheckDeclaredTypeRules(declared, ctx, names_covergroup);
    ValidateVirtualInterfaceType(declared.type, declared.loc, find_module,
                                 ctx.diag);
  });
}

}  // namespace

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl,
                                           RtlirModule* mod) {
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  replicate_multiplier_scope_ = scope;
  streaming_slice_size_scope_ = scope;
  array_query_dim_scope_ = scope;
  array_arg_dim_scope_ = scope;
  pla_ascending_scope_ = procedural_typedef_scope_ = scope;
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item, *mod, scope);
  }
  using DeclCheck = void (Elaborator::*)(const ModuleDecl*);
  using PlainCheck = void (Elaborator::*)();
  static constexpr DeclCheck kDeclChecks[] = {
      &Elaborator::ValidatePackageImportRules,
      &Elaborator::ValidateScopeRules,
      nullptr,
      &Elaborator::ValidateInputPortAssignments,
      &Elaborator::ValidatePatterns,
      &Elaborator::ValidateDisableTargets,
      &Elaborator::ValidateFinalTaskEnables,
      nullptr,
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
      &Elaborator::ValidateRefArgActuals,
      &Elaborator::ValidateArrayArgTypes,
      &Elaborator::ValidateLocalProtectedAccess,
      &Elaborator::ValidateConstPropertyWritesFromOutside,
      &Elaborator::ValidateParameterizedScopeResolution,
      &Elaborator::ValidateRestrictedScopePrefixUsage,
      &Elaborator::ValidateStaticMethodBodies,
      &Elaborator::ValidateClassMethodBodies,
      &Elaborator::ValidateThisUsage,
  };
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
  CheckIsunboundedArgs(decl, mod, diag_);
  CheckTimeformatArgs(decl, diag_);
  InstanceParams instance_params;
  for (const auto& param : mod->params) {
    if (!param.gen_block_prefix.empty()) continue;
    if (param.is_unbounded) instance_params.unbounded.insert(param.name);
    if (param.from_override) instance_params.overridden.insert(param.name);
  }
  CheckDollarOperands(decl, *unit_, instance_params, diag_);
  CheckVariableReadsInUnpackedDims(decl, var_types_, diag_);
  CheckUntypedDefaultPatternValues(decl, diag_);
  CheckContinuousPropertyWrites(decl, class_var_types_, unit_, diag_);
  CheckInstanceLocalTypeAssignments(decl, unit_, diag_);
  CheckNettypeUses(decl, *unit_, nettype_names_, diag_);
  CheckNewPlacement(decl, diag_);
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  CheckInnerDeclaredTypes(
      decl, {kShapeTables, &scope, diag_},
      [this](std::string_view name) { return FindModuleInScope(name); },
      [this, mod](std::string_view name) {
        return mod != nullptr && VisibleCovergroup(name, mod, unit_) != nullptr;
      });
}

namespace {

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

DeclaredTimescale DeclaredBy(bool has_timescale, const TimeScale& ts) {
  return {{has_timescale, ts.unit, ts.magnitude},
          {has_timescale, ts.precision, ts.prec_magnitude}};
}

struct TimescaleScan {
  bool any_specified = false;
  bool any_unspecified = false;
  SourceLoc unspecified_loc;
};

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

void CheckTimescaleOrder(const TimeScale& ts, SourceLoc loc, DiagEngine& diag) {
  if (EffectiveTimeOrder(ts.precision, ts.prec_magnitude) >
      EffectiveTimeOrder(ts.unit, ts.magnitude)) {
    diag.Error(loc, "time precision is less precise than the time unit",
               Subclause("3.14"));
  }
}

void CheckDesignElementTimescales(const ModuleDecl* decl, bool nested,
                                  const CompilationUnit& unit,
                                  DiagEngine& diag) {
  if (decl->is_extern) return;
  bool inherits_whole =
      nested && !decl->has_timeunit && !decl->has_timeprecision;
  if (!inherits_whole) {
    CheckTimescaleOrder(ModuleTimescale(decl, unit), decl->range.start, diag);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl) {
      CheckDesignElementTimescales(item->nested_module_decl, true, unit, diag);
    }
  }
}

}  // namespace

static void ScanTimescaleElements(const CompilationUnit* unit,
                                  TimescaleScan& scan) {
  DeclaredTimescale cu = DeclaredBy(unit);

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
  for (const auto* pkg : unit->packages) {
    ClassifyTimescaleElement(
        DeclaredBy(pkg),
        DeclaredBy(pkg->has_directive_timescale, pkg->directive_timescale), cu,
        pkg->range.start, scan);
  }
}

void Elaborator::ValidateTimescaleConsistency() {
  TimescaleScan scan;
  UnitScopeTables::ForEachUnit(*this,
                               [&] { ScanTimescaleElements(unit_, scan); });

  if (scan.any_specified && scan.any_unspecified) {
    diag_.Error(scan.unspecified_loc,
                "some design elements specify time unit and precision while "
                "others do not",
                Subclause("3.14.2.3"));
  }
}

void Elaborator::ValidateTimescaleOrder() {
  for (const auto* list :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (const auto* decl : *list) {
      CheckDesignElementTimescales(decl, false, *unit_, diag_);
    }
  }
  const TimeScale kUnitScale = CompilationUnitTimescale(*unit_);
  for (const auto* pkg : unit_->packages) {
    CheckTimescaleOrder(PackageTimescale(*pkg, kUnitScale), pkg->range.start,
                        diag_);
  }
}

}  // namespace delta
