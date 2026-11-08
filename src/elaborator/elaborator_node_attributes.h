#pragma once

#include <functional>

#include "elaborator/const_eval.h"

namespace delta {

class DiagEngine;
struct ModuleItem;
struct RtlirDesign;
struct RtlirModule;

void RecordNodeAttributes(const ModuleItem& item, RtlirModule& mod,
                          DiagEngine& diag,
                          const std::function<ScopeMap()>& params);

void RecordModportAttributes(RtlirModule& mod, DiagEngine& diag,
                             const std::function<ScopeMap()>& params);

void RecordDesignAttributes(RtlirDesign& design, DiagEngine& diag,
                            const ScopeMap& params);

}  // namespace delta
