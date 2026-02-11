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

/// Evaluate the bit width of a struct/union member.
struct StructMember;
uint32_t EvalStructMemberWidth(const StructMember& m);

/// Overload that resolves kNamed types via the typedef map.
uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs);

/// Return true if the type kind uses 4-state values (0, 1, x, z).
/// logic, reg, integer are 4-state.  bit, int, byte, etc. are 2-state.
bool Is4stateType(DataTypeKind kind);

/// Overload that resolves kNamed types via the typedef map.
bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

// Forward declarations
struct Expr;

/// Return true if two types match (IEEE §6.22.1).
bool TypesMatch(const DataType& a, const DataType& b);

/// Return true if two types are equivalent (IEEE §6.22.2).
bool TypesEquivalent(const DataType& a, const DataType& b);

/// Return true if type a is assignment compatible with type b (IEEE §6.22.3).
bool IsAssignmentCompatible(const DataType& a, const DataType& b);

/// Return true if type a is cast compatible with type b (IEEE §6.22.4).
bool IsCastCompatible(const DataType& a, const DataType& b);

/// Infer the self-determined width of an expression (IEEE §11.6).
/// Returns 0 for expressions that can't be sized.
uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs);

/// Apply context-determined width: propagate assignment LHS width to RHS.
uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs);

}  // namespace delta
