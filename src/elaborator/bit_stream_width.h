#pragma once

#include <cstdint>
#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct Expr;

// The number of elements one unpacked dimension gives, written `[size]` or
// `[left:right]` with bounds that fold in `scope`; nullopt for a dynamic `[]`,
// queue `[$]` or associative dimension, and for bounds that do not fold.
std::optional<uint32_t> FixedDimElementCount(const Expr* dim,
                                             const ScopeMap& scope);

// The number of elements a declaration's unpacked dimensions give it, each
// folding with no parameter in scope; zero where one does not fold to a fixed
// size, a dynamic, queue or associative dimension among them.
uint32_t FixedUnpackedElementCount(const std::vector<Expr*>& dims);

// §6.24.3 (printed page 142): the size of a fixed-size bit-stream type is the
// number of bits it holds, an unpacked structure's being every bit of every
// member, so its `byte command [2]` holds sixteen. EvalTypeWidth gives such a
// member the width of one element, so an unpacked structure is summed here,
// each member's element size times its element count, and any other type is
// EvalTypeWidth's. Zero where a member's size is not fixed.
uint32_t BitStreamTypeWidth(const DataType& type, const TypedefMap& typedefs);

}  // namespace delta
