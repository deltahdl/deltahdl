#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/packed_range.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
class SimContext;
struct ArrayInfo;
struct RtlirVariable;
struct Expr;
struct StructFieldInfo;

struct PatternKeyType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = 0;
  bool is_signed = false;
  PackedRange range = {};
  std::string_view name = {};
};

struct PatternKeySubject {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = 0;
  std::optional<bool> is_signed = std::nullopt;
  std::string_view type_name = {};
  std::optional<PackedRange> range = std::nullopt;
  bool is_array = false;
};

DataTypeKind PatternKeyKeywordKind(std::string_view key);

std::optional<PatternKeyType> ResolvePatternKeyType(std::string_view key,
                                                    const SimContext& ctx);

bool PatternKeyMatches(const PatternKeyType& key,
                       const PatternKeySubject& subject);

PatternKeySubject SubjectOf(PatternKeySubject subject, const SimContext& ctx);

PatternKeySubject SubjectOfElement(const ArrayInfo& info,
                                   const SimContext& ctx);

PatternKeySubject SubjectOfField(const StructFieldInfo& field,
                                 const SimContext& ctx);

PatternKeySubject SubjectOfVariableElement(const RtlirVariable& var,
                                           SimContext& ctx, Arena& arena);

void RecordElementType(ArrayInfo& info, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena);

bool PatternHasTypeKey(const Expr* pattern, const SimContext& ctx);

const Expr* IndexKeyedItem(const Expr* pattern, uint32_t idx, SimContext& ctx,
                           Arena& arena);
const Expr* TypeKeyedItem(const Expr* pattern, const PatternKeySubject& subject,
                          const SimContext& ctx);
const Expr* DefaultKeyedItem(const Expr* pattern);

}  // namespace delta
