#pragma once

#include <functional>

#include "elaborator/const_eval.h"

namespace delta {

class DiagEngine;
struct ModuleItem;
struct RtlirModule;

// §5.12 with §37.83: resolve the attribute instances written on `item`, where
// it is a kind whose attributes no record of its own keeps, and on every
// statement its body holds, into RtlirModule::node_attrs of `mod`, each value
// folded against the scope `params` gives, asked for only where an attribute
// is written.
void RecordNodeAttributes(const ModuleItem& item, RtlirModule& mod,
                          DiagEngine& diag,
                          const std::function<ScopeMap()>& params);

}  // namespace delta
