#include "simulator/vpi_value_numbers.h"

#include <cstdint>

#include "common/types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_user.h"

namespace delta {

int64_t VpiKnownIntegerValue(const Logic4Vec& v) {
  const uint64_t kBits = v.ToUint64();
  if (!v.is_signed || v.width == 0 || v.width >= 64) {
    return static_cast<int64_t>(kBits);
  }
  const uint64_t kSign = uint64_t{1} << (v.width - 1);
  const uint64_t kLow = kBits & ((kSign << 1) - 1);
  return static_cast<int64_t>((kLow ^ kSign) - kSign);
}

int VpiObjTypeFormat(int type) {
  if (type == vpiIntegerVar || type == vpiIntVar) return kVpiIntVal;
  if (type == vpiTimeVar) return kVpiTimeVal;
  return kVpiObjTypeVal;
}

}  // namespace delta
