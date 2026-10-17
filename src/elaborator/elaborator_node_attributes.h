#pragma once

#include <functional>

#include "elaborator/const_eval.h"

namespace delta {

class DiagEngine;
struct ModuleItem;
struct RtlirDesign;
struct RtlirModule;

// §5.12 with §37.83: resolve the attribute instances written on `item`, where
// it is a kind whose attributes no record of its own keeps, on every
// statement its body holds and operator its expressions hold, and on a class
// it declares and that class's items, into RtlirModule::node_attrs of `mod`,
// each value folded against the scope `params` gives, asked for only where an
// attribute is written.
void RecordNodeAttributes(const ModuleItem& item, RtlirModule& mod,
                          DiagEngine& diag,
                          const std::function<ScopeMap()>& params);

// §5.12 with §37.83: resolve the attribute instances written on each class
// the compilation unit or a package declares, and on its items, into
// RtlirDesign::node_attrs of `design`, folded against `params`, the
// compilation unit's parameters and those its packages make visible.
void RecordDesignClassAttributes(RtlirDesign& design, DiagEngine& diag,
                                 const ScopeMap& params);

}  // namespace delta
