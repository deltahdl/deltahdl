#pragma once

#include <optional>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"

namespace delta {

// §6.23 (printed page 138) with §6.7.1 and §23.2.2.3: the data type of the net
// or variable `mod` records under `declared`, which a type reference to the
// value stands for: the type its declaration writes, logic where that writes
// no data type, with the signing and packed dimensions it does write, and for
// a net a port declares, the port's. Nothing where `mod` records neither of
// the name, where the name is an enumeration's named constant, and where the
// value has an unpacked dimension, which the written type does not carry.
std::optional<DataType> NetOrVariableType(const RtlirModule& mod,
                                          std::string_view declared);

}  // namespace delta
