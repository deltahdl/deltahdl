#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_region_lines.h"

namespace delta {

// §34.5.10, §34.5.16 and §34.5.23 hold the values written against the names
// designating one entity's key unique for that entity, as an ENCRYPTION INPUT
// constraint. Reports, at `opened`, each entity of the region a value was
// written against two of those names for.
void ReportRepeatedDesignations(const RegionKeyReader& in_effect,
                                DiagEngine* diag, SourceLoc opened);

// §34.5.13, §34.5.19 and §34.5.26 have a public key and a name written for one
// entity's key refer to the same key. Reports, at `opened`, each pair of the
// region's that reaches two different keys of `keys`.
void ReportDisagreeingDesignations(const RegionKeyNames& names,
                                   const ProtectKeyList& keys, DiagEngine* diag,
                                   SourceLoc opened);

}  // namespace delta
