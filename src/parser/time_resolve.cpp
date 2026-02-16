#include "parser/time_resolve.h"

#include <cctype>

namespace delta {

bool TryParseTimeUnit(std::string_view text, TimeUnit& out) {
  size_t i = 0;
  while (i < text.size() &&
         (std::isdigit(static_cast<unsigned char>(text[i])) || text[i] == '.'))
    ++i;
  return ParseTimeUnitStr(text.substr(i), out);
}

// §3.14.2.3 precedence resolution
ResolvedTimescale ResolveModuleTimescale(const ModuleDecl* mod,
                                         const CompilationUnit* cu,
                                         bool has_preproc_timescale,
                                         const TimeScale& preproc_timescale,
                                         const ResolvedTimescale* enclosing) {
  ResolvedTimescale result;

  // Resolve time unit using rules (a)-(d).
  if (mod->has_timeunit) {
    // Module explicitly specifies timeunit — use it.
    result.unit = mod->time_unit;
    result.has_unit = true;
  } else if (enclosing != nullptr && enclosing->has_unit) {
    // Rule (a): inherit from enclosing module/interface.
    result.unit = enclosing->unit;
    result.has_unit = true;
  } else if (has_preproc_timescale) {
    // Rule (b): use last `timescale directive in CU.
    result.unit = preproc_timescale.unit;
    result.has_unit = true;
  } else if (cu->has_cu_timeunit) {
    // Rule (c): use CU-scope timeunit declaration.
    result.unit = cu->cu_time_unit;
    result.has_unit = true;
  }
  // Rule (d): default — result.unit stays kNs, has_unit stays false.

  // Resolve time precision following same precedence (§3.14.2.3).
  if (mod->has_timeprecision) {
    result.precision = mod->time_prec;
    result.has_precision = true;
  } else if (enclosing != nullptr && enclosing->has_precision) {
    result.precision = enclosing->precision;
    result.has_precision = true;
  } else if (has_preproc_timescale) {
    result.precision = preproc_timescale.precision;
    result.has_precision = true;
  } else if (cu->has_cu_timeprecision) {
    result.precision = cu->cu_time_prec;
    result.has_precision = true;
  }

  return result;
}

}  // namespace delta
