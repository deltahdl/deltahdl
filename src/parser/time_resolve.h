#pragma once

#include <string_view>

#include "common/types.h"
#include "parser/ast_design.h"

namespace delta {

bool TryParseTimeUnit(std::string_view text, TimeUnit& out);

bool TryParseTimeMagnitudeAndUnit(std::string_view text, int& magnitude,
                                  TimeUnit& out);

TimeUnit ComputeGlobalTimePrecision(const CompilationUnit* cu,
                                    bool has_preproc_global_precision,
                                    TimeUnit preproc_global_precision);

int GlobalTimePrecisionOrder(const CompilationUnit* cu);

}  // namespace delta
