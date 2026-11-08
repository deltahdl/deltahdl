#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"

namespace delta {

struct DataType;
enum class DataTypeKind : uint8_t;
class Arena;
struct PackageDecl;
struct ClassDecl;
struct ModuleItem;

using TypedefMap = std::unordered_map<std::string_view, DataType>;

void ResolveNestedAggregateTypes(DataType& dt, const TypedefMap& typedefs,
                                 Arena& arena);

void SizeClassHandleMembers(
    DataType& dt, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names);

const DataType* ResolvedAggregateType(const DataType& dtype,
                                      const TypedefMap& typedefs,
                                      const ScopeMap& scope, Arena& arena);

const DataType* NamedPackedVectorType(const DataType& dtype,
                                      const TypedefMap& typedefs, Arena& arena);

void FoldMemberDims(DataType& type, const ScopeMap& scope, Arena& arena);

uint32_t PackedDimProduct(const DataType& dtype);

uint32_t PackedDimProduct(const DataType& dtype, const ScopeMap& scope);

uint32_t EvalTypeWidth(const DataType& dtype);

DataType EnumArrayElement(const DataType& dtype);

bool IsStringType(const DataType& type, const TypedefMap& typedefs);

bool IsTypeKeyword(std::string_view key);
bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind);

inline constexpr uint32_t kStringMemberHandleWidth = 64;

inline constexpr uint32_t kDynamicMemberHandleWidth = 64;

inline constexpr uint32_t kClassMemberHandleWidth = 64;

struct StructMember;
uint32_t EvalStructMemberWidth(const StructMember& m);
uint32_t UnpackedMemberCount(const StructMember& m);
bool IsDynamicArrayMember(const StructMember& m);
uint32_t StructMemberStorageWidth(const StructMember& m);
bool UnpackedMemberBounds(const StructMember& m, int64_t* left, int64_t* right);
uint32_t EvalStructMemberWidth(const StructMember& m,
                               const TypedefMap& typedefs);
uint32_t StructMemberStorageWidth(const StructMember& m,
                                  const TypedefMap& typedefs);
uint32_t CombinedMemberWidth(
    const DataType& dtype,
    const std::function<uint32_t(const StructMember&)>& member_width);
uint32_t EvalStructOrUnionWidth(const DataType& dtype,
                                const TypedefMap& typedefs);
uint32_t FoldedMembersWidth(const DataType& dtype, const TypedefMap& typedefs,
                            const ScopeMap& scope);

uint32_t TaggedUnionTagWidth(const DataType& dtype);
uint32_t TaggedUnionTagBitOffset(const DataType& dtype);

std::vector<std::string_view> OuterScopePrefixes(const DataType& dt);

std::string TypeChainKey(const DataType& type);

const DataType* FindNamedType(const DataType& dtype,
                              const TypedefMap& typedefs);

std::optional<DataType> ThroughBoundPrefix(const DataType& dtype,
                                           const TypedefMap& typedefs);

void RecordTypedef(TypedefMap& typedefs, std::string_view name,
                   const DataType& type);

DataType InPackageScope(const DataType& type, const PackageDecl& package);

DataType InClassScope(const DataType& type, const ClassDecl& cls);

DataType InClassScope(const DataType& type, const ClassDecl& cls,
                      std::string_view scope);

using TypedefScopes = std::unordered_map<std::string_view, std::string_view>;

DataType InTypedefScopes(const DataType& type, const TypedefScopes& scopes,
                         Arena& arena);

void EnterTypedefScope(TypedefScopes& scopes, const ModuleItem& td,
                       std::string_view scope);

DataType PackageTypedefType(const ModuleItem& item, const PackageDecl& pkg,
                            Arena& arena);

const DataType& LastTypeInChain(const DataType& dtype,
                                const TypedefMap& typedefs);

DataTypeKind ResolvedTypeKind(const DataType& dtype,
                              const TypedefMap& typedefs);

const DataType* TypeAtChainEnd(const DataType& dtype,
                               const TypedefMap& typedefs);

const DataType* MemberNamedType(const StructMember& m,
                                const TypedefMap& typedefs);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs,
                       const ScopeMap& scope);

bool Is4stateType(DataTypeKind kind);

bool IsImplicitlySigned(DataTypeKind kind);

DataType TypeNameToDataType(std::string_view name);

bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

bool IsSignedType(const DataType& dtype, const TypedefMap& typedefs);

struct Expr;

bool IsVector(const DataType& dtype);

bool IsVector(const DataType& dtype, const TypedefMap& typedefs);

bool IsSingularType(const DataType& dtype);

bool IsAggregateType(const DataType& dtype);

bool IsSingularType(const DataType& dtype, const TypedefMap& typedefs);

bool IsAggregateType(const DataType& dtype, const TypedefMap& typedefs);

bool WeakRefTypeParamNamesClass(
    const DataType& tp, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names);

bool IsIntegralType(DataTypeKind kind);

bool IsMemberlessKind(DataTypeKind kind);

bool IsNetTypeKind(DataTypeKind kind);

bool IsSimpleBitVectorType(DataTypeKind kind);

bool IsSimpleBitVectorType(const DataType& dtype);

bool IsUnpackedAggregateType(const DataType& type);

bool TypesMatch(const DataType& a, const DataType& b);
bool TypesMatch(const DataType& a, const DataType& b, const ScopeMap& scope);

bool TypesEquivalent(const DataType& a, const DataType& b);

struct ElementTypeInfo {
  DataTypeKind kind;
  uint32_t width;
  bool is_signed;
  bool is_4state;
  std::string_view type_name;
};

bool ElementTypesEquivalent(const ElementTypeInfo& a, const ElementTypeInfo& b);

bool IsAssignmentCompatible(const DataType& a, const DataType& b);

bool IsCastCompatible(const DataType& a, const DataType& b);

bool IsTypeIncompatible(const DataType& a, const DataType& b);

uint32_t CastTargetWidth(std::string_view type_name);

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs);

uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs);

}  // namespace delta
