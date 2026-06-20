#pragma once

#include <string>
#include <string_view>
#include <vector>

namespace delta {

struct LibPin {
  std::string name;
  std::string direction;
  std::string function;
};

struct LibTiming {
  std::string related_pin;
  float cell_rise = 0.0f;
  float cell_fall = 0.0f;
};

struct LibCell {
  std::string name;
  float area = 0.0f;
  std::vector<LibPin> pins;
  std::vector<LibTiming> timing;
};

struct Liberty {
  std::string library_name;
  std::vector<LibCell> cells;
};

Liberty ParseLiberty(std::string_view source);

}  // namespace delta
