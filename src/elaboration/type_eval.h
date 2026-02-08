#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>

namespace delta {

// Forward declarations
struct DataType;
enum class DataTypeKind : uint8_t;

/// Map from typedef name to its underlying DataType.
using TypedefMap = std::unordered_map<std::string_view, DataType>;

/// Evaluate the bit width of a data type.
/// Returns 1 for implicit/unsized types.
uint32_t EvalTypeWidth(const DataType& dtype);

/// Overload that resolves kNamed types via the typedef map.
uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs);

/// Return true if the type kind uses 4-state values (0, 1, x, z).
/// logic, reg, integer are 4-state.  bit, int, byte, etc. are 2-state.
bool Is4stateType(DataTypeKind kind);

/// Overload that resolves kNamed types via the typedef map.
bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

}  // namespace delta
