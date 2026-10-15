#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "simulator/sdf_parser.h"

namespace delta {

// §32.5: the SDF source one annotation is taken from -- the cell whose entry is
// being applied, the file it sits in, which an INTERCONNECT entry resolves its
// port names against, and the instance prefix the cell's CELLINSTANCE names.
//
// `inst_prefix` is what SdfCellPrefixInRegion (simulator/sdf_parser.h) made of
// the cell's instance path, read from the §32.9 region down: the
// hierarchical prefix of the module instance whose specify block declared the
// paths this cell annotates, in the spelling PathDelay::inst_prefix carries.
struct SdfCellSource {
  const SdfCell& cell;
  const SdfFile& file;
  std::string_view inst_prefix;
};

// The member of an SDF value's min:typ:max triple `mtm` selects, as the
// unsigned quantity a delay, a limit or a specparam value holds, a value
// written negative reading as 0 (§30.5.1).
uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm);

// The same member with the sign the file wrote in front of it (§32.7).
int64_t SelectSignedMtm(const SdfDelayValue& dv, SdfMtm mtm);

// §32.3 and §32.5: whether `dv` provides no value for `mtm` to select -- it was
// written as empty parentheses, or as a triple leaving that member out -- so
// what it stands for is held rather than annotated.
bool SdfValueHeld(const SdfDelayValue& dv, SdfMtm mtm);

// §32.4.1 (printed page 925) and §32.4.2: an SDF port written with a select,
// `a[1]` or `b[3:2]`, as the bare name a terminal is recorded under and the
// select as written; the whole spelling as the name, and no select, where it
// carries none.
void SplitSdfPortSelect(const std::string& port, std::string& name,
                        std::string& select);

}  // namespace delta
