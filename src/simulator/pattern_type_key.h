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

// §10.9.1 and §10.9.2 (printed pages 262 and 264): the type an assignment
// pattern's type key names -- a built-in type keyword or a typedef name in
// scope (Syntax 10-5's simple_type) -- as the simulator compares it with an
// element's or a member's type: its kind, its width, its signing, the bounds
// of its outermost packed dimension, and the typedef name it was written as,
// empty for a keyword.
struct PatternKeyType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = 0;
  bool is_signed = false;
  PackedRange range = {};
  std::string_view name = {};
};

// What a type key is matched against: an array element's or a structure
// member's type. The signing and the range are empty where the maker of the
// element or member did not record them; SubjectOf fills them in.
struct PatternKeySubject {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = 0;
  std::optional<bool> is_signed = std::nullopt;
  std::string_view type_name = {};
  std::optional<PackedRange> range = std::nullopt;
  bool is_array = false;
};

// The type `key` names, or nothing where it names no type -- an index or a
// member name, or `default`.
std::optional<PatternKeyType> ResolvePatternKeyType(std::string_view key,
                                                    const SimContext& ctx);

// Whether `key` matches `subject` as §6.22.1 has types match: the same typedef
// name, or for integral types the same state, signing and packed bounds, so
// `logic` does not match `logic [7:0]`, nor `logic [7:0]` `logic [8:1]`, and
// `int` matches a typedef of int; a structure, union or enum type only itself,
// and any other type the same kind. `subject` is one SubjectOf has filled in.
bool PatternKeyMatches(const PatternKeyType& key,
                       const PatternKeySubject& subject);

// `subject` with its kind resolved through the typedef it was written as
// where the kind is that name, and with the signing its kind or typedef gives
// and the range its typedef or its width gives where none was recorded.
PatternKeySubject SubjectOf(PatternKeySubject subject, const SimContext& ctx);

// The subject an element of the array `info` describes presents.
PatternKeySubject SubjectOfElement(const ArrayInfo& info,
                                   const SimContext& ctx);

// The subject a structure member presents, and for an unpacked array member
// the type of one of its elements.
PatternKeySubject SubjectOfField(const StructFieldInfo& field,
                                 const SimContext& ctx);

// The subject an element of the array variable `var` presents, its range
// folded from the packed dimension its declaration writes.
PatternKeySubject SubjectOfVariableElement(const RtlirVariable& var,
                                           SimContext& ctx, Arena& arena);

// Records on `info` the element type of the array variable `var`: its kind,
// the typedef name it was written as, its signing and its packed bounds.
void RecordElementType(ArrayInfo& info, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena);

// Whether any key of `pattern` names a type.
bool PatternHasTypeKey(const Expr* pattern, const SimContext& ctx);

// §10.9.1's three matching rules for an element of an array, each the item
// of `pattern` it gives the element, null where it gives none:
//
// the item an index key naming address `idx` gives -- the clause makes naming
// one index twice an error, so the first such key is the only one that can;
const Expr* IndexKeyedItem(const Expr* pattern, uint32_t idx, SimContext& ctx,
                           Arena& arena);
// the item a type key matching `subject` gives, the last of several matching
// keys giving it;
const Expr* TypeKeyedItem(const Expr* pattern, const PatternKeySubject& subject,
                          const SimContext& ctx);
// and the item the default key gives, which covers the elements no index key
// and no type key matched.
const Expr* DefaultKeyedItem(const Expr* pattern);

}  // namespace delta
