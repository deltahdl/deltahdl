#pragma once

#include <cstddef>
#include <string>

namespace delta {

class Arena;
class SimContext;
struct ClockingBlock;
struct RtlirGenBlockClocking;
struct RtlirModule;

// §14.3 with §27.4: the entry recording the clocking block at `index` in
// `mod`'s clocking_blocks as declared in a generate block, or null for a block
// of the module itself.
const RtlirGenBlockClocking* FindGenBlockClocking(const RtlirModule* mod,
                                                  size_t index);

// The prefix of the innermost generate block instance `gen` stands in, or an
// empty one for a block of the module itself (a null `gen`).
std::string GenBlockClockingPrefix(const RtlirGenBlockClocking* gen);

// §14.3 with §27.4 and §23.9: places `block`, built as a block of its module
// instance, in the generate block instance `gen` records. The block is
// registered under that instance's prefix, since each instance of a loop block
// declares one of its own, and the bare names of its clock and its signals are
// resolved as a reference written in the instance resolves them, the
// instance's own declaration ahead of the module's. Nothing for a null `gen`.
void PlaceClockingBlockInGenBlock(const RtlirGenBlockClocking* gen,
                                  ClockingBlock& block, SimContext& ctx,
                                  Arena& arena);

// §23.6: makes the registered `block` and its event answer to the path that
// names it from outside its generate block, `g.cb` or `u.g[1].cb`, where that
// path has a name for every block on it (§27.6). Nothing for a null `gen`.
void AliasGenBlockClockingBlock(const RtlirGenBlockClocking* gen,
                                const ClockingBlock& block, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
