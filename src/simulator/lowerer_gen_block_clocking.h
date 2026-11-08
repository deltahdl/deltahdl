#pragma once

#include <cstddef>
#include <string>

namespace delta {

class Arena;
class SimContext;
struct ClockingBlock;
struct RtlirGenBlockClocking;
struct RtlirModule;

const RtlirGenBlockClocking* FindGenBlockClocking(const RtlirModule* mod,
                                                  size_t index);

std::string GenBlockClockingPrefix(const RtlirGenBlockClocking* gen);

void PlaceClockingBlockInGenBlock(const RtlirGenBlockClocking* gen,
                                  ClockingBlock& block, SimContext& ctx,
                                  Arena& arena);

void AliasGenBlockClockingBlock(const RtlirGenBlockClocking* gen,
                                const ClockingBlock& block, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
