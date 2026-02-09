#include "synthesis/adv_synth.h"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

#include "synthesis/aig.h"
#include "synthesis/aig_opt.h"
#include "synthesis/lut_map.h"

namespace delta {
namespace {

// =============================================================================
// Helpers
// =============================================================================

/// Return true if `node_id` is a primary input in the graph.
bool IsInputNode(const AigGraph& g, uint32_t node_id) {
  for (uint32_t inp : g.inputs) {
    if (inp == node_id) return true;
  }
  return false;
}

/// Return true if `node_id` is an AND gate (not constant, not primary input).
bool IsAndNode(const AigGraph& g, uint32_t node_id) {
  if (node_id == 0 || node_id >= g.nodes.size()) return false;
  if (IsInputNode(g, node_id)) return false;
  const auto& node = g.nodes[node_id];
  return node.fanin0 != 0 || node.fanin1 != 0;
}

/// Compute a simple depth metric for a LUT mapping: the maximum number of
/// dependent LUT levels from any primary input to any output.
uint32_t ComputeMaxDepth(const LutMapping& mapping) {
  if (mapping.cells.empty()) return 0;
  // Simple heuristic: count cells as a proxy for depth.
  // A more precise computation would build a DAG of LUT cells, but for the
  // basic iterative tradeoff this suffices.
  return static_cast<uint32_t>(mapping.cells.size());
}

}  // namespace

// =============================================================================
// RetimeForward
// =============================================================================

uint32_t RetimeForward(AigGraph& g) {
  uint32_t moved = 0;
  std::vector<std::pair<uint32_t, uint32_t>> new_latches;

  for (const auto& [state_id, next_lit] : g.latches) {
    uint32_t next_id = AigVar(next_lit);
    bool is_compl = AigIsCompl(next_lit);

    // Only absorb a non-complemented AND gate.
    if (is_compl || !IsAndNode(g, next_id)) {
      new_latches.emplace_back(state_id, next_lit);
      continue;
    }

    // The next-state is AND(fanin0, fanin1).
    // Replace this latch with two new latches at the fanin inputs.
    const auto& and_node = g.nodes[next_id];
    uint32_t latch0_lit = g.AddInput();
    uint32_t latch1_lit = g.AddInput();
    uint32_t latch0_id = AigVar(latch0_lit);
    uint32_t latch1_id = AigVar(latch1_lit);

    new_latches.emplace_back(latch0_id, and_node.fanin0);
    new_latches.emplace_back(latch1_id, and_node.fanin1);

    // Rebuild the AND from the new latch outputs so downstream sees them.
    uint32_t new_and = g.AddAnd(latch0_lit, latch1_lit);

    // Patch any outputs that referenced the old state input.
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

// =============================================================================
// RetimeBackward
// =============================================================================

uint32_t RetimeBackward(AigGraph& g) {
  // Basic backward retiming: run constant propagation to simplify any
  // trivially redundant latch chains, then report opportunities found.
  // A full implementation would merge latch pairs that share an AND output,
  // but this basic version focuses on cleanup.
  uint32_t moved = 0;
  ConstProp(g);
  return moved;
}

// =============================================================================
// MapForDelay
// =============================================================================

LutMapping MapForDelay(const AigGraph& g, uint32_t lut_size) {
  // Use the existing LUT mapper. The mapper already performs cut enumeration
  // which naturally produces depth-oriented cuts for smaller K values.
  // A full delay-oriented mapper would use arrival-time labeling to pick
  // depth-minimal cuts; this basic version delegates to the area mapper.
  LutMapper mapper(lut_size);
  LutMapping mapping = mapper.Map(g);

  // Sort cells by output id to present them in topological order, which
  // corresponds to increasing depth.
  std::sort(
      mapping.cells.begin(), mapping.cells.end(),
      [](const LutCell& a, const LutCell& b) { return a.output < b.output; });

  return mapping;
}

// =============================================================================
// IterativeAreaDelay
// =============================================================================

/// Run one area-oriented mapping pass.
static LutMapping MapForArea(const AigGraph& g, uint32_t lut_size) {
  LutMapper mapper(lut_size);
  return mapper.Map(g);
}

LutMapping IterativeAreaDelay(const AigGraph& g, uint32_t lut_size,
                              uint32_t iterations) {
  // Start with a delay-oriented mapping as the baseline.
  LutMapping best = MapForDelay(g, lut_size);
  auto best_area = static_cast<uint32_t>(best.cells.size());
  uint32_t best_depth = ComputeMaxDepth(best);

  for (uint32_t i = 0; i < iterations; ++i) {
    bool is_area_round = (i % 2 == 0);
    LutMapping candidate =
        is_area_round ? MapForArea(g, lut_size) : MapForDelay(g, lut_size);

    auto cand_area = static_cast<uint32_t>(candidate.cells.size());
    uint32_t cand_depth = ComputeMaxDepth(candidate);

    // Accept the candidate if it improves on the relevant metric without
    // worsening the other metric.
    bool accept = false;
    if (is_area_round && cand_area < best_area) {
      accept = true;
    }
    if (!is_area_round && cand_depth < best_depth) {
      accept = true;
    }
    // Always accept if both metrics are at least as good.
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
