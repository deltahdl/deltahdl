#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "simulator/sdf_parser.h"

namespace delta {

struct SdfCellSource {
  const SdfCell& cell;
  const SdfFile& file;
  std::string_view inst_prefix;
};

uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm);

int64_t SelectSignedMtm(const SdfDelayValue& dv, SdfMtm mtm);

bool SdfValueHeld(const SdfDelayValue& dv, SdfMtm mtm);

void SplitSdfPortSelect(const std::string& port, std::string& name,
                        std::string& select);

}  // namespace delta
