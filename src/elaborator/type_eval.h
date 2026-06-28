#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>

#include "elaborator/const_eval.h"

namespace delta {

struct DataType;
enum class DataTypeKind : uint8_t;

using TypedefMap = std::unordered_map<std::string_view, DataType>;

uint32_t EvalTypeWidth(const DataType& dtype);

struct StructMember;
uint32_t EvalStructMemberWidth(const StructMember& m);
uint32_t EvalStructMemberWidth(const StructMember& m,
                               const TypedefMap& typedefs);

uint32_t TaggedUnionTagWidth(const DataType& dtype);
uint32_t TaggedUnionTagBitOffset(const DataType& dtype);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs,
                       const ScopeMap& scope);

bool Is4stateType(DataTypeKind kind);

bool IsImplicitlySigned(DataTypeKind kind);

// §6.20.3/§6.23: map a type name (a built-in keyword like `int`/`shortint` or a
// user type/class name) to a DataType. Built-in scalar types map to their kind
// with the kind's implicit signedness; any other name becomes a kNamed type
// that resolves against the class/typedef tables later.
DataType TypeNameToDataType(std::string_view name);

bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

bool IsSignedType(const DataType& dtype, const TypedefMap& typedefs);

struct Expr;

bool IsVector(const DataType& dtype);

bool IsVector(const DataType& dtype, const TypedefMap& typedefs);

bool IsSingularType(const DataType& dtype);

bool IsAggregateType(const DataType& dtype);

bool IsIntegralType(DataTypeKind kind);

bool IsSimpleBitVectorType(DataTypeKind kind);

bool IsSimpleBitVectorType(const DataType& dtype);

bool TypesMatch(const DataType& a, const DataType& b);

bool TypesEquivalent(const DataType& a, const DataType& b);

// §6.22.2 — the element-type descriptor compared when deciding whether two
// array element types are equivalent: the kind, packed bit width, signedness,
// and whether the element is 4-state.
struct ElementTypeInfo {
  DataTypeKind kind;
  uint32_t width;
  bool is_signed;
  bool is_4state;
};

bool ElementTypesEquivalent(const ElementTypeInfo& a, const ElementTypeInfo& b);

bool IsAssignmentCompatible(const DataType& a, const DataType& b);

bool IsCastCompatible(const DataType& a, const DataType& b);

bool IsTypeIncompatible(const DataType& a, const DataType& b);

// Returns the bit width implied by a cast target type name (built-in keyword or
// a leading decimal width such as "12"); returns 0 for "string" and any name
// that has no fixed bit width. Defined once in type_eval.cpp.
uint32_t CastTargetWidth(std::string_view type_name);

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs);

uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs);

}  // namespace delta
