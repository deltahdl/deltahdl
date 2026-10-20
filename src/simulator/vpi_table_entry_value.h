#pragma once

#include <string_view>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

// §38.15: the vpiVectorVal value of a UDP table entry whose row reads as
// `row` (§37.36 detail 1) -- its symbols in order, input fields, then the
// current state of a sequential row, then the output, two bytes each, four to
// an element: the most significant then the least significant half of aval,
// then of bval. A symbol's first character is the higher of its two bytes,
// and a one-character symbol's second byte is NUL.
std::vector<s_vpi_vecval> VpiTableEntryVector(std::string_view row);

}  // namespace delta
