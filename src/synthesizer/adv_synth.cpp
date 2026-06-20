#include "synthesizer/adv_synth.h"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

#include "synthesizer/aig.h"
#include "synthesizer/aig_opt.h"
#include "synthesizer/lut_map.h"

namespace delta {
namespace {

bool IsInputNode(const AigGraph& g, uint32_t node_id) {
  for (uint32_t inp : g.inputs) {
    if (inp == node_id) return true;
  }
  return false;
}

bool IsAndNode(const AigGraph& g, uint32_t node_id) {
  if (node_id == 0 || node_id >= g.nodes.size()) return false;
  if (IsInputNode(g, node_id)) return false;
  const auto& node = g.nodes[node_id];
  return node.fanin0 != 0 || node.fanin1 != 0;
}

uint32_t ComputeMaxDepth(const LutMapping& mapping) {
  if (mapping.cells.empty()) return 0;

  return static_cast<uint32_t>(mapping.cells.size());
}

}  // namespace

uint32_t RetimeForward(AigGraph& g) {
  uint32_t moved = 0;
  std::vector<std::pair<uint32_t, uint32_t>> new_latches;

  for (const auto& [state_id, next_lit] : g.latches) {
    uint32_t next_id = AigVar(next_lit);
    bool is_compl = AigIsCompl(next_lit);

    if (is_compl || !IsAndNode(g, next_id)) {
      new_latches.emplace_back(state_id, next_lit);
      continue;
    }

    const auto& and_node = g.nodes[next_id];
    uint32_t latch0_lit = g.AddInput();
    uint32_t latch1_lit = g.AddInput();
    uint32_t latch0_id = AigVar(latch0_lit);
    uint32_t latch1_id = AigVar(latch1_lit);

    new_latches.emplace_back(latch0_id, and_node.fanin0);
    new_latches.emplace_back(latch1_id, and_node.fanin1);

    uint32_t new_and = g.AddAnd(latch0_lit, latch1_lit);

    uint32_t old_state_lit = AigLit(state_id, false);
    for (auto& out : g.outputs) {
      if (out == old_state_lit) out = new_and;
      if (out == (old_state_lit ^ 1u)) out = g.AddNot(new_and);
    }
    ++moved;
  }

  g.latches = std::move(new_latches);
  return moved;
}

uint32_t RetimeBackward(AigGraph& g) {
  uint32_t moved = 0;
  ConstProp(g);
  return moved;
}

LutMapping MapForDelay(const AigGraph& g, uint32_t lut_size) {
  LutMapper mapper(lut_size);
  LutMapping mapping = mapper.Map(g);

  std::sort(
      mapping.cells.begin(), mapping.cells.end(),
      [](const LutCell& a, const LutCell& b) { return a.output < b.output; });

  return mapping;
}

static LutMapping MapForArea(const AigGraph& g, uint32_t lut_size) {
  LutMapper mapper(lut_size);
  return mapper.Map(g);
}

LutMapping IterativeAreaDelay(const AigGraph& g, uint32_t lut_size,
                              uint32_t iterations) {
  LutMapping best = MapForDelay(g, lut_size);
  auto best_area = static_cast<uint32_t>(best.cells.size());
  uint32_t best_depth = ComputeMaxDepth(best);

  for (uint32_t i = 0; i < iterations; ++i) {
    bool is_area_round = (i % 2 == 0);
    LutMapping candidate =
        is_area_round ? MapForArea(g, lut_size) : MapForDelay(g, lut_size);

    auto cand_area = static_cast<uint32_t>(candidate.cells.size());
    uint32_t cand_depth = ComputeMaxDepth(candidate);

    bool accept = false;
    if (is_area_round && cand_area < best_area) {
      accept = true;
    }
    if (!is_area_round && cand_depth < best_depth) {
      accept = true;
    }

    if (cand_area <= best_area && cand_depth <= best_depth) {
      accept = true;
    }

    if (accept) {
      best = std::move(candidate);
      best_area = cand_area;
      best_depth = cand_depth;
    }
  }

  return best;
}

}  // namespace delta
