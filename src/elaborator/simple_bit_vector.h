#pragma once

#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/net_data_type.h"

namespace delta {

struct DataType;

// §6.11.1 (printed page 109): a simple bit vector type is one that directly
// represents a one-dimensional packed array of bits: an integer type of Table
// 6-8, or bit, logic or reg with at most one packed dimension. A packed
// structure or union, an enumeration, a multidimensional packed array and
// anything with an unpacked dimension are not, nor is a non-integral type.
// Judges `dtype` as what its typedef names stand for, counting the packed
// dimensions each name adds. An implicit type is the logic vector its range
// gives. A class name is no bit vector, and any other name that resolves to
// nothing leaves nothing to judge and is taken as one.
bool IsSimpleBitVectorType(const DataType& dtype,
                           const TypeShapeTables& tables);

// §6.20.7 (printed page 131): `$` may be assigned only to a value parameter of
// a simple bit vector type, which an untyped parameter is, its type following
// its value. Reports the parameter `name`, declared with `dtype` (null when
// untyped) and with unpacked dimensions when `has_unpacked_dims`, when its
// type is not one.
void ValidateUnboundedParamType(std::string_view name, const DataType* dtype,
                                bool has_unpacked_dims,
                                const TypeShapeTables& tables, DiagEngine& diag,
                                SourceLoc loc);

}  // namespace delta
