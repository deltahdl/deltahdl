#pragma once

#include <string_view>
#include <vector>

namespace delta {

struct FsmDecl {
  std::vector<std::string_view> state_signals;
  bool has_part_select = false;
  int msb = 0;
  int lsb = 0;
  std::string_view fsm_name;
  std::string_view enum_name;
  std::vector<std::string_view> states;
};

}  // namespace delta
