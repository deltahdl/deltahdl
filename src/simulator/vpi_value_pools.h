#pragma once

#include <deque>
#include <string>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

struct VpiValuePools {
  std::vector<std::string> strings;
  std::vector<std::vector<s_vpi_vecval>> vectors;
  std::vector<std::vector<s_vpi_strengthval>> strengths;
  std::deque<s_vpi_time> times;
};

}  // namespace delta
