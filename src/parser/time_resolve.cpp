#include "parser/time_resolve.h"

#include <cctype>
#include <cstddef>
#include <string_view>

#include "common/types.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

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

namespace {

// The finest precision found so far, as its order: 10ps is -11.
struct FinestOrder {
  int order = 0;
  bool found = false;

  void Update(TimeUnit unit, int magnitude) {
    int candidate = EffectiveTimeOrder(unit, magnitude);
    if (!found || candidate < order) {
      order = candidate;
      found = true;
    }
  }
};

}  // namespace

static void CollectModulePrecisions(const ModuleDecl* mod,
                                    FinestOrder& finest) {
  if (mod->has_timeprecision) {
    finest.Update(mod->time_prec, mod->time_prec_magnitude);
  }

  for (const auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      CollectModulePrecisions(item->nested_module_decl, finest);
    }
  }
}

// §3.14.3: the finest of every precision the unit declares, `preproc` holding
// that of the `timescale directives where any was read.
static FinestOrder CollectGlobalPrecision(const CompilationUnit* cu,
                                          const FinestOrder& preproc) {
  FinestOrder finest = preproc;

  if (cu->has_cu_timeprecision) {
    finest.Update(cu->cu_time_prec, cu->cu_time_prec_magnitude);
  }

  for (const auto* mod : cu->modules) {
    CollectModulePrecisions(mod, finest);
  }
  for (const auto* iface : cu->interfaces) {
    CollectModulePrecisions(iface, finest);
  }
  for (const auto* prog : cu->programs) {
    CollectModulePrecisions(prog, finest);
  }
  for (const auto* pkg : cu->packages) {
    if (pkg->has_timeprecision) {
      finest.Update(pkg->time_prec, pkg->time_prec_magnitude);
    }
  }

  return finest;
}

TimeUnit ComputeGlobalTimePrecision(const CompilationUnit* cu,
                                    bool has_preproc_global_precision,
                                    TimeUnit preproc_global_precision) {
  FinestOrder preproc;
  if (has_preproc_global_precision) preproc.Update(preproc_global_precision, 1);
  FinestOrder finest = CollectGlobalPrecision(cu, preproc);
  if (!finest.found) return TimeUnit::kNs;
  // The unit of an order is the power of 1000 at or below it: -11 is ps.
  return static_cast<TimeUnit>(finest.order - (finest.order % 3 + 3) % 3);
}

int GlobalTimePrecisionOrder(const CompilationUnit* cu) {
  FinestOrder preproc;
  if (cu->has_preproc_global_precision) {
    preproc.Update(cu->preproc_global_precision,
                   cu->preproc_global_precision_magnitude);
  }
  FinestOrder finest = CollectGlobalPrecision(cu, preproc);
  return finest.found ? finest.order : EffectiveTimeOrder(TimeUnit::kNs, 1);
}

}  // namespace delta
