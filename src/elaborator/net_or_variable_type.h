#pragma once

#include <optional>
#include <string_view>

#include "elaborator/expression_self_type.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"

namespace delta {

// §6.23 (printed page 138) with §6.7.1 and §23.2.2.3: the data type of the net
// or variable `mod` records under `declared`, which a type reference to the
// value stands for: the type its declaration writes, logic where that writes
// no data type, with the signing and packed dimensions it does write, and for
// a port, the type the port's declaration writes. Nothing where `mod` records
// no net, variable or port of the name, where the name is an enumeration's
// named constant or an interface port, and where the value has an unpacked
// dimension, which the written type does not carry.
std::optional<DataType> NetOrVariableType(const RtlirModule& mod,
                                          std::string_view declared);

// §7.4.2 with §6.23: the same value with the number of unpacked dimensions it
// is declared with, which a select of it addresses first; a dynamic array, a
// queue and an associative array count one where the declaration's count is
// not recorded. Nothing where `mod` records no net, variable or port of the
// name, and where the name is an enumeration's named constant or an interface
// port.
std::optional<DeclaredValue> NetOrVariableValue(const RtlirModule& mod,
                                                std::string_view declared);

}  // namespace delta
