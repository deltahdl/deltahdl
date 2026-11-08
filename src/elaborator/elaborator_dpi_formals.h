#pragma once

#include "common/diagnostic.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/type_eval.h"

namespace delta {

struct ModuleItem;

void CheckImportFormalTypedefTypes(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

void CheckImportFormalUnpackedDims(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

void CheckExportFormalUnpackedDims(const ModuleItem* callable,
                                   const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

}  // namespace delta
