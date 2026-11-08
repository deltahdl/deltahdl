#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

namespace delta {

int32_t DpiRuntime::SvLow(const SvOpenArrayHandle& h) { return h.low; }

int32_t DpiRuntime::SvHigh(const SvOpenArrayHandle& h) { return h.high; }

uint32_t DpiRuntime::SvSize(const SvOpenArrayHandle& h) { return h.size; }

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromPackedActual(
    void* actual_data, uint32_t actual_bits, uint32_t elem_width) {
  return SvOpenArrayHandle{
      actual_data, actual_bits, elem_width, 0,
      actual_bits > 0 ? static_cast<int32_t>(actual_bits - 1) : 0};
}

uint32_t DpiRuntime::LinearizedPackedSize(
    const std::vector<SvActualDimension>& packed_dims) {
  uint64_t size = packed_dims.empty() ? 0 : 1;
  for (const SvActualDimension& dim : packed_dims) {
    const int64_t kValues =
        std::abs(static_cast<int64_t>(dim.high) - dim.low) + 1;
    size *= static_cast<uint64_t>(kValues);
  }
  return static_cast<uint32_t>(size);
}

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromPackedActual(
    void* actual_data, const std::vector<SvActualDimension>& packed_dims,
    uint32_t elem_width) {
  return MakeOpenArrayFromPackedActual(
      actual_data, LinearizedPackedSize(packed_dims), elem_width);
}

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromUnpackedActual(
    void* actual_data, SvActualDimension actual, uint32_t elem_width) {
  int64_t values = static_cast<int64_t>(actual.high) - actual.low + 1;
  return SvOpenArrayHandle{actual_data,
                           static_cast<uint32_t>(std::max<int64_t>(values, 0)),
                           elem_width, actual.low, actual.high};
}

}  // namespace delta
