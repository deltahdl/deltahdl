#pragma once

#include <string>
#include <vector>

#include "synthesizer/aig.h"
#include "synthesizer/liberty.h"

namespace delta {

struct CellInstance {
  std::string cell_name;
  std::vector<std::string> input_nets;
  std::string output_net;
};

struct CellMapping {
  std::vector<CellInstance> instances;
};

class CellMapper {
 public:
  explicit CellMapper(const Liberty& lib);

  CellMapping Map(const AigGraph& aig) const;

 private:
  const Liberty& lib_;
};

}  // namespace delta
