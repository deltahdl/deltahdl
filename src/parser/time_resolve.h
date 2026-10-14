#pragma once

#include <string_view>

#include "common/types.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

bool TryParseTimeUnit(std::string_view text, TimeUnit& out);

bool TryParseTimeMagnitudeAndUnit(std::string_view text, int& magnitude,
                                  TimeUnit& out);

ResolvedTimescale ResolveModuleTimescale(const ModuleDecl* mod,
                                         const CompilationUnit* cu,
                                         bool has_preproc_timescale,
                                         const TimeScale& preproc_timescale,
                                         const ResolvedTimescale* enclosing);

TimeUnit ComputeGlobalTimePrecision(const CompilationUnit* cu,
                                    bool has_preproc_timescale,
                                    TimeUnit preproc_global_precision);

// §3.14.3: the order of the global time precision, the finest precision of
// every `timescale directive, compilation-unit, module, interface, program and
// package declaration of `cu`, each with its magnitude: 10ps is -11. 1ns when
// none is declared.
int GlobalTimePrecisionOrder(const CompilationUnit* cu);

}  // namespace delta
