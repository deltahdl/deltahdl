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

bool ElementTypesEquivalent(DataTypeKind a_kind, uint32_t a_width,
                            bool a_signed, bool a_4state, DataTypeKind b_kind,
                            uint32_t b_width, bool b_signed, bool b_4state);

bool IsAssignmentCompatible(const DataType& a, const DataType& b);

bool IsCastCompatible(const DataType& a, const DataType& b);

bool IsTypeIncompatible(const DataType& a, const DataType& b);

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs);

uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs);

}
