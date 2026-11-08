#pragma once

#include <vector>

#include "elaborator/property_instance.h"
#include "parser/ast_stmt.h"

namespace delta {

class Arena;
class DiagEngine;
struct ModuleItem;
class PropertyRegistry;
struct RtlirModule;
struct RtlirProcess;

void ElaborateProceduralConcurrentAssertions(ModuleItem* procedure,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag);

std::vector<EventExpr> ProcessInferredClock(const RtlirProcess& proc,
                                            const RtlirModule* mod);

InferredAtInstance InferredInProcedure(const ModuleItem* procedure,
                                       const RtlirModule* mod);

void ReportUnclockedLetSampledValues(const ModuleItem* procedure,
                                     const RtlirModule* mod, DiagEngine& diag);

void ElaborateSubroutineConcurrentAssertions(ModuleItem* subroutine,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag);

}  // namespace delta
