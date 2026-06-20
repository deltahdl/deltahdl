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

bool TryParseTimeMagnitudeAndUnit(std::string_view text, int& magnitude,
                                  TimeUnit& out) {
  size_t i = 0;
  while (i < text.size() && std::isdigit(static_cast<unsigned char>(text[i]))) {
    ++i;
  }
  if (i == 0) return false;
  int mag = 0;
  for (size_t j = 0; j < i; ++j) {
    mag = mag * 10 + (text[j] - '0');
  }
  if (mag != 1 && mag != 10 && mag != 100) return false;
  if (!ParseTimeUnitStr(text.substr(i), out)) return false;
  magnitude = mag;
  return true;
}

ResolvedTimescale ResolveModuleTimescale(const ModuleDecl* mod,
                                         const CompilationUnit* cu,
                                         bool has_preproc_timescale,
                                         const TimeScale& preproc_timescale,
                                         const ResolvedTimescale* enclosing) {
  ResolvedTimescale result;

  if (mod->has_timeunit) {
    result.unit = mod->time_unit;
    result.has_unit = true;
  } else if (enclosing != nullptr && enclosing->has_unit) {
    result.unit = enclosing->unit;
    result.has_unit = true;
  } else if (has_preproc_timescale) {
    result.unit = preproc_timescale.unit;
    result.has_unit = true;
  } else if (cu->has_cu_timeunit) {
    result.unit = cu->cu_time_unit;
    result.has_unit = true;
  }

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

  if (has_preproc_timescale) {
    UpdateMin(preproc_global_precision, result, found);
  }

  if (cu->has_cu_timeprecision) {
    UpdateMin(cu->cu_time_prec, result, found);
  }

  for (const auto* mod : cu->modules) {
    CollectModulePrecisions(mod, result, found);
  }
  for (const auto* iface : cu->interfaces) {
    CollectModulePrecisions(iface, result, found);
  }
  for (const auto* prog : cu->programs) {
    CollectModulePrecisions(prog, result, found);
  }
  for (const auto* pkg : cu->packages) {
    if (pkg->has_timeprecision) {
      UpdateMin(pkg->time_prec, result, found);
    }
  }

  return result;
}

}  // namespace delta
