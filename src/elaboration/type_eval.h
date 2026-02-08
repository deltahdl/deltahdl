#pragma once

#include <cstdint>

namespace delta {

// Forward declarations
struct DataType;
enum class DataTypeKind : uint8_t;

/// Evaluate the bit width of a data type.
/// Returns 1 for implicit/unsized types.
uint32_t EvalTypeWidth(const DataType& dtype);

/// Return true if the type kind uses 4-state values (0, 1, x, z).
/// logic, reg, integer are 4-state.  bit, int, byte, etc. are 2-state.
bool Is4stateType(DataTypeKind kind);

}  // namespace delta
