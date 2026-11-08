#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_region_lines.h"

namespace delta {

void ReportRepeatedDesignations(const RegionKeyReader& in_effect,
                                DiagEngine* diag, SourceLoc opened);

void ReportDisagreeingDesignations(const RegionKeyNames& names,
                                   const ProtectKeyList& keys, DiagEngine* diag,
                                   SourceLoc opened);

}  // namespace delta
