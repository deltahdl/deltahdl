#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"

namespace delta {

static uint64_t ReduceSumVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result += v;
  return result;
}

static uint64_t ReduceProductVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 1;
  for (auto v : vals) result *= v;
  return result;
}

static uint64_t ReduceAndVals(const std::vector<uint64_t>& vals) {
  uint64_t result = vals.empty() ? 0 : vals[0];
  for (size_t i = 1; i < vals.size(); ++i) result &= vals[i];
  return result;
}

static uint64_t ReduceOrVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result |= v;
  return result;
}

static uint64_t ReduceXorVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result ^= v;
  return result;
}

uint64_t ApplyReduction(std::string_view method,
                        const std::vector<uint64_t>& vals) {
  if (method == "sum") return ReduceSumVals(vals);
  if (method == "product") return ReduceProductVals(vals);
  if (method == "and") return ReduceAndVals(vals);
  if (method == "or") return ReduceOrVals(vals);
  if (method == "xor") return ReduceXorVals(vals);
  return 0;
}

bool OrdersBefore(const Logic4Vec& a, const Logic4Vec& b, bool is_signed) {
  if (!is_signed) return a.ToUint64() < b.ToUint64();
  return SignExtend(a.ToUint64(), a.width) < SignExtend(b.ToUint64(), b.width);
}

}  // namespace delta
