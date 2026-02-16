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

// §3.14.3 — global time precision is min of all precision sources.
static void UpdateMin(TimeUnit candidate, TimeUnit& current, bool& found) {
  if (!found || static_cast<int>(candidate) < static_cast<int>(current)) {
    current = candidate;
    found = true;
  }
}

static void CollectModulePrecisions(const ModuleDecl* mod, TimeUnit& current,
                                    bool& found) {
  if (mod->has_timeprecision) {
    UpdateMin(mod->time_prec, current, found);
  }
  // Recurse into nested modules/interfaces.
  for (const auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      CollectModulePrecisions(item->nested_module_decl, current, found);
    }
  }
}

TimeUnit ComputeGlobalTimePrecision(const CompilationUnit* cu,
                                    bool has_preproc_timescale,
                                    TimeUnit preproc_global_precision) {
  TimeUnit result = TimeUnit::kNs;
  bool found = false;

  // Consider `timescale precision (preprocessor already tracks global min).
  if (has_preproc_timescale) {
    UpdateMin(preproc_global_precision, result, found);
  }

  // Consider CU-scope timeprecision.
  if (cu->has_cu_timeprecision) {
    UpdateMin(cu->cu_time_prec, result, found);
  }

  // Consider all modules, interfaces, programs.
  for (const auto* mod : cu->modules) {
    CollectModulePrecisions(mod, result, found);
  }
  for (const auto* iface : cu->interfaces) {
    CollectModulePrecisions(iface, result, found);
  }
  for (const auto* prog : cu->programs) {
    CollectModulePrecisions(prog, result, found);
  }

  return result;
}

}  // namespace delta
