#include <algorithm>
#include <cstdint>

#include "simulator/dpi_runtime.h"

namespace delta {

// §35.6.1.1: "The unsized ranges of open arrays are determined at a call site",
// so the range is settled by whichever of the two factories below the call site
// went through and these only report what the handle already carries.
int32_t DpiRuntime::SvLow(const SvOpenArrayHandle& h) { return h.low; }

int32_t DpiRuntime::SvHigh(const SvOpenArrayHandle& h) { return h.high; }

uint32_t DpiRuntime::SvSize(const SvOpenArrayHandle& h) { return h.size; }

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromPackedActual(
    void* actual_data, uint32_t actual_bits, uint32_t elem_width) {
  // §35.6.1.1: the formal's solitary unsized packed dimension takes the
  // linearized size of the actual's packed dimensions and the normalized range
  // over it; the element width is the type information carried over from the
  // import declaration.
  return SvOpenArrayHandle{
      actual_data, actual_bits, elem_width, 0,
      actual_bits > 0 ? static_cast<int32_t>(actual_bits - 1) : 0};
}

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromUnpackedActual(
    void* actual_data, SvActualDimension actual, uint32_t elem_width) {
  // §35.6.1.1: the formal's unsized unpacked dimension takes on the actual
  // dimension's own range, so the bounds pass through and the size is however
  // many values that range holds. The subtraction is widened and the count
  // floored at zero because the bounds are the caller's: SystemVerilog declares
  // no empty unpacked dimension, and a high below its low would otherwise be a
  // size read out of an underflow rather than the empty handle it describes.
  int64_t values = static_cast<int64_t>(actual.high) - actual.low + 1;
  return SvOpenArrayHandle{actual_data,
                           static_cast<uint32_t>(std::max<int64_t>(values, 0)),
                           elem_width, actual.low, actual.high};
}

}  // namespace delta
