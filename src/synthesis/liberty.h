#pragma once

#include <string>
#include <string_view>
#include <vector>

namespace delta {

// --- Liberty (.lib) file parser ---
//
// Simplified parser for Liberty timing libraries. Extracts the key constructs
// needed for standard-cell mapping: cell definitions, pin declarations with
// logic functions, timing arcs, and area values.

/// A pin within a Liberty cell.
struct LibPin {
  std::string name;
  std::string direction;  // "input" or "output"
  std::string function;   // Boolean expression (e.g., "A * B", "!A")
};

/// A timing arc within a Liberty cell.
struct LibTiming {
  std::string related_pin;
  float cell_rise = 0.0f;
  float cell_fall = 0.0f;
};

/// A cell within a Liberty library.
struct LibCell {
  std::string name;
  float area = 0.0f;
  std::vector<LibPin> pins;
  std::vector<LibTiming> timing;
};

/// A parsed Liberty library.
struct Liberty {
  std::string library_name;
  std::vector<LibCell> cells;
};

/// Parse a Liberty (.lib) source string into a Liberty structure.
Liberty ParseLiberty(std::string_view source);

}  // namespace delta
