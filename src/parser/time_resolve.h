#pragma once

#include <string_view>

#include "parser/ast.h"

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

}  // namespace delta
