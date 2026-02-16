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

}  // namespace delta
