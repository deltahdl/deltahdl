#include "simulator/lowerer_gen_block_clocking.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"
#include "simulator/clocking.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

std::string_view ResolveInGenBlock(std::string_view path,
                                   const RtlirGenBlockClocking& gen,
                                   std::string_view inst_prefix,
                                   SimContext& ctx, Arena& arena) {
  if (path.empty() || path.find('.') != std::string_view::npos) return path;
  const GenBlockPrefixes& prefixes = gen.gen_block_prefixes;
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    std::string key =
        std::string(inst_prefix) + std::string(*it) + std::string(path);
    if (ctx.FindVariable(key) == nullptr && ctx.FindNet(key) == nullptr) {
      continue;
    }
    return *arena.Create<std::string>(key.substr(inst_prefix.size()));
  }
  return path;
}

}  // namespace

const RtlirGenBlockClocking* FindGenBlockClocking(const RtlirModule* mod,
                                                  size_t index) {
  for (const RtlirGenBlockClocking& gen : mod->gen_block_clocking) {
    if (gen.index == index) return &gen;
  }
  return nullptr;
}

std::string GenBlockClockingPrefix(const RtlirGenBlockClocking* gen) {
  if (gen == nullptr || gen->gen_block_prefixes.empty()) return {};
  return std::string(gen->gen_block_prefixes.back());
}

void PlaceClockingBlockInGenBlock(const RtlirGenBlockClocking* gen,
                                  ClockingBlock& block, SimContext& ctx,
                                  Arena& arena) {
  if (gen == nullptr || gen->gen_block_prefixes.empty()) return;
  std::string_view inst_prefix = block.inst_prefix;
  block.name = *arena.Create<std::string>(
      std::string(inst_prefix) + GenBlockClockingPrefix(gen) +
      std::string(block.name.substr(inst_prefix.size())));
  block.clock_signal =
      ResolveInGenBlock(block.clock_signal, *gen, inst_prefix, ctx, arena);
  for (ClockingSignal& sig : block.signals) {
    if (sig.target_expr != nullptr) continue;
    std::string_view path =
        sig.target_path.empty() ? sig.signal_name : sig.target_path;
    std::string_view resolved =
        ResolveInGenBlock(path, *gen, inst_prefix, ctx, arena);
    if (resolved != path) sig.target_path = resolved;
  }
}

void AliasGenBlockClockingBlock(const RtlirGenBlockClocking* gen,
                                const ClockingBlock& block, SimContext& ctx,
                                Arena& arena) {
  if (gen == nullptr || gen->gen_block_path.empty() ||
      gen->block->name.empty()) {
    return;
  }
  for (const HierStep& step : gen->gen_block_path) {
    if (step.name.empty()) return;
  }
  auto* key = arena.Create<std::string>(std::string(block.inst_prefix) +
                                        GenBlockName(gen->gen_block_path) +
                                        "." + std::string(gen->block->name));
  ctx.AcquireClockingManager().AddBlockAlias(*key, block.name);
  ctx.AliasVariable(*key, block.name);
}

}  // namespace delta
