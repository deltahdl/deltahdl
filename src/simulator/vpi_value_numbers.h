#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

int64_t VpiKnownIntegerValue(const Logic4Vec& v);

int VpiObjTypeFormat(int type);

}  // namespace delta
