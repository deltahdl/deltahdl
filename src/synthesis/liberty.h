#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// --- Liberty (.lib) cell library representation ---
//
// Minimal representation of a standard cell library parsed from
// Synopsys Liberty format files. Used by the ASIC cell mapper to
// select gate implementations during technology mapping.

struct CellPin {
    std::string name;
    std::string direction;    // "input", "output", "inout"
    std::string function;     // Boolean function string (e.g., "A & B")
    double max_transition = 0.0;
    double capacitance = 0.0;
};

struct Cell {
    std::string name;
    double area = 0.0;
    std::vector<CellPin> pins;
};

struct CellLibrary {
    std::string name;
    std::vector<Cell> cells;
};

// --- Liberty file parser ---

class LibertyParser {
public:
    /// Parse a Liberty (.lib) file and return the cell library.
    CellLibrary parse(std::string_view filename);
};

} // namespace delta
