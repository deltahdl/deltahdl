#pragma once

#include <string_view>

#include "parser/ast.h"

namespace delta {

// Extract time unit suffix from a time literal like "1ns", "100us".
bool TryParseTimeUnit(std::string_view text, TimeUnit& out);

// §3.14.2.3 precedence resolution for a module's effective timescale.
ResolvedTimescale ResolveModuleTimescale(const ModuleDecl* mod,
                                         const CompilationUnit* cu,
                                         bool has_preproc_timescale,
                                         const TimeScale& preproc_timescale,
                                         const ResolvedTimescale* enclosing);

// §3.14.3 — Compute the global time precision (simulation time unit).
// This is the minimum of all timeprecision statements, all precision
// arguments to timeunit declarations, and the smallest `timescale precision.
// preproc_global_precision: the preprocessor's min of all `timescale
// precisions.
TimeUnit ComputeGlobalTimePrecision(const CompilationUnit* cu,
                                    bool has_preproc_timescale,
                                    TimeUnit preproc_global_precision);

}  // namespace delta
