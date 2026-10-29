#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

// The kind of array an unpacked dimension makes: one of a fixed size, or a
// dynamic array (§7.5), a queue (§7.10) or an associative array (§7.8), each
// element of which is an element of a dynamic object.
enum class UnpackedKind : std::uint8_t {
  kFixed,
  kDynamic,
  kQueue,
  kAssociative
};

// §7.4 (printed page 153): the kind of array the unpacked dimension `dim`
// makes, as the parser keeps it: a dynamic array's `[]` as no dimension, a
// queue's `[$]` and `[$:N]` as an identifier `$`, a constant range or size as
// the expression written, and an associative index as its index type.
UnpackedKind UnpackedDimKind(const Expr* dim, const TypeShapeTables& tables);

// §7.8: the index type the associative dimension `dim` writes: a typedef's or
// a class's name, bare or behind a package's or class's scope, a built-in type
// with the signing and packed dimensions written after its keyword, or the
// type a type reference written as the index stands for. Nothing for the
// wildcard `[*]`, which has no index type.
std::optional<DataType> IndexDimType(const Expr* dim);

// An unpacked array type (§7.4): the type of its elements and its unpacked
// dimensions, outermost first, each as its declaration writes it. A type of
// no unpacked dimension is its element type alone.
struct UnpackedArrayType {
  DataType element;
  std::vector<Expr*> dims;
};

// §7.4.4 with §6.18: `element` under the unpacked dimensions `dims`, read
// through each typedef name it is written with, a typedef of an unpacked array
// adding its dimensions inside those `dims` holds, so that `row m [2]` under
// `typedef byte row [3]` is a byte array of dimensions [2][3]. A name past the
// last typedef that writes a dimension is left as written.
UnpackedArrayType WithTypedefDims(const DataType& element,
                                  std::vector<Expr*> dims,
                                  const TypeShapeTables& tables);

// §6.22.1: whether two data types match, each name they are written with read
// through first; nothing where a name resolves to no type.
using TypeMatcher =
    std::function<std::optional<bool>(const DataType&, const DataType&)>;

// §6.22.1(f) (printed page 135): whether `a` and `b` match: as many unpacked
// dimensions, each pair of the same kind of array, with matching index types
// where associative and the same left and right bounds where fixed in size,
// `[n]` standing for `[0:n-1]` (§7.4.2), and element types that match. Bounds
// fold against `constants` and types are matched by `match`; nothing where a
// bound does not fold or `match` gives nothing.
std::optional<bool> UnpackedArrayTypesMatch(const UnpackedArrayType& a,
                                            const UnpackedArrayType& b,
                                            const TypeShapeTables& tables,
                                            const ScopeMap& constants,
                                            const TypeMatcher& match);

}  // namespace delta
