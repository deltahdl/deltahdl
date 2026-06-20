#pragma once

#include <cstdint>
#include <vector>

#include "synthesizer/aig.h"

namespace delta {

struct LutCell {
  uint32_t output = 0;
  std::vector<uint32_t> inputs;
  uint64_t truth_table = 0;
};

struct LutMapping {
  std::vector<LutCell> cells;
  uint32_t lut_size = 4;
};

struct Cut {
  std::vector<uint32_t> leaves;
};

class LutMapper {
 public:
  explicit LutMapper(uint32_t lut_size = 4);

  LutMapping Map(const AigGraph& aig);

 private:
  uint32_t lut_size_;
};

}  // namespace delta
