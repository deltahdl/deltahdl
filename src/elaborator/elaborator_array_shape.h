#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

// §6.22.2 a) makes a typedef name equivalent to the type it names, so an
// element type written through one is recorded as the kind its chain of
// typedef names ends at, `bit` for `uint10` of `typedef bit [10:1] uint10;`,
// and §7.6's element comparison reaches item d)'s test of width, state and
// signedness. A name with no definition is kept, and so is one naming an
// enumeration, which item d) does not reach and which the integral comparison
// would take for its base type; the hop limit keeps a cyclic typedef from
// looping.
DataTypeKind ElementKindThroughTypedefs(const DataType& dtype,
                                        const TypedefMap& typedefs);

// §7.4.2 with §7.7: the shape of an unpacked array, one entry per unpacked
// dimension in declaration order. An entry is the dimension's size where it is
// written as a size or a range whose bounds fold in `scope`, and nullopt where
// the dimension has no size of its own: a dynamic `[]` or queue `[$]`
// dimension, an associative index, or bounds that do not fold. An element type
// that is a typedef naming an unpacked aggregate (one of `aggregate_typedefs`)
// brings further dimensions the declaration does not write, so for such an
// element the shape is not known and is returned empty.
std::vector<std::optional<uint32_t>> UnpackedShapeOf(
    const DataType& elem, const std::vector<Expr*>& dims,
    const std::unordered_set<std::string_view>& aggregate_typedefs,
    const ScopeMap& scope);

}  // namespace delta
