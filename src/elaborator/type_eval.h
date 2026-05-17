#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>

#include "elaborator/const_eval.h"

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

/// Overload that also resolves parameter identifiers in dimension ranges.
uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs,
                        const ScopeMap& scope);

// The integer data types from §6.11 Table 6-8 (logic, reg, bit, byte,
// shortint, int, longint, integer, time) are classified along two orthogonal
// axes — Is4stateType (§6.11.2) and IsImplicitlySigned (§6.11.3) — kept
// adjacent here so a change to the Table 6-8 set touches both predicates.

/// §6.11.2: Return true if the type kind uses 4-state values (0, 1, x, z).
/// logic, reg, integer, time are 4-state.  bit, int, byte, etc. are 2-state.
bool Is4stateType(DataTypeKind kind);

/// §6.11.3: Return true if the type kind is signed by default per Table 6-8.
/// byte, shortint, int, longint, integer default to signed; the unsigned-by-
/// default integer types are time, bit, reg, and logic (and arrays thereof).
bool IsImplicitlySigned(DataTypeKind kind);

/// Overload that resolves kNamed types via the typedef map.
bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

/// Overload that resolves kNamed types via the typedef map.
bool IsSignedType(const DataType& dtype, const TypedefMap& typedefs);

// Forward declarations
struct Expr;

/// §6.9: Return true if the type denotes a *vector*. §6.9 normatively
/// defines a vector as a multibit reg/logic/bit (or implicitly logic)
/// declared with a range, and states that "Vectors are packed arrays of
/// scalars" — so the predicate requires exactly one packed dimension (no
/// extra_packed_dims) and an element kind in {logic, reg, bit, implicit}.
bool IsVector(const DataType& dtype);

/// §6.9: Overload that resolves *matching user-defined types* through the
/// typedef map. §6.9's enumeration of vector element types explicitly
/// includes "a matching user-defined type", so a typedef whose underlying
/// type is a one-dimensional packed reg/logic/bit is itself a §6.9 vector.
bool IsVector(const DataType& dtype, const TypedefMap& typedefs);

/// §6.4: Return true if the data type is singular (not an unpacked struct,
/// unpacked union, or unpacked array).  Packed structs/unions are singular.
bool IsSingularType(const DataType& dtype);

/// §6.4: Return true if the data type is aggregate (unpacked struct, unpacked
/// union, or unpacked array).
bool IsAggregateType(const DataType& dtype);

/// §6.11.1: Return true if the type kind represents an integral type.
bool IsIntegralType(DataTypeKind kind);

/// §6.11.1: Return true if the type kind represents a *simple bit vector type*.
/// §6.11.1 defines a simple bit vector type as one that can directly represent
/// a one-dimensional packed array of bits; the integer types listed in
/// Table 6-8 (bit, logic, reg, byte, shortint, int, longint, integer, time)
/// are simple bit vector types with predefined widths.
bool IsSimpleBitVectorType(DataTypeKind kind);

/// §6.11.1: Overload that rejects packed structures (§7.2.1), packed unions
/// (§7.2.2), and multidimensional packed array types (§7.4) — each is
/// equivalent to a simple bit vector type but is not itself one.
bool IsSimpleBitVectorType(const DataType& dtype);

/// Return true if two types match (IEEE §6.22.1).
bool TypesMatch(const DataType& a, const DataType& b);

/// Return true if two types are equivalent (IEEE §6.22.2).
bool TypesEquivalent(const DataType& a, const DataType& b);

/// §6.22.2: Element-type equivalence for §7.6 array assignment compatibility.
/// Two integral element types are equivalent under rules (a) and (c) when they
/// have the same width, same signedness, and same 2-state/4-state class. For
/// non-integral kinds equivalence reduces to kind+signedness equality.
bool ElementTypesEquivalent(DataTypeKind a_kind, uint32_t a_width,
                            bool a_signed, bool a_4state, DataTypeKind b_kind,
                            uint32_t b_width, bool b_signed, bool b_4state);

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
