#pragma once

namespace delta {

class DiagEngine;
struct ModuleItem;

void ReportMisplacedOverrideSpecifiers(const ModuleItem& item,
                                       DiagEngine& diag);

}  // namespace delta
