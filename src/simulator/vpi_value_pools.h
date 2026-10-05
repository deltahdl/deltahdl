#pragma once

#include <deque>
#include <string>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

// §38.15: the memory vpi_get_value() provides for the str, time, vector and
// strength members of the value union it fills, valid at least until the next
// call. VpiContext owns one of these; it stands apart from the context so that
// what the routine hands out is declared in one place. What each retrieval
// hands out is kept here until the context is torn down: an array in an inner
// vector of its own and a time in a deque, neither of which a later retrieval
// moves.
struct VpiValuePools {
  std::vector<std::string> strings;
  std::vector<std::vector<s_vpi_vecval>> vectors;
  std::vector<std::vector<s_vpi_strengthval>> strengths;
  std::deque<s_vpi_time> times;
};

}  // namespace delta
