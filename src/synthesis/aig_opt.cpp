#include "synthesis/aig_opt.h"

#include <cstdint>
#include <vector>

namespace delta {

// =============================================================================
// Constant propagation
// =============================================================================

static bool IsConst(uint32_t lit) {
  return lit == AigGraph::kConstFalse || lit == AigGraph::kConstTrue;
}

static uint32_t SimplifyAnd(uint32_t f0, uint32_t f1, uint32_t orig) {
  if (f0 == AigGraph::kConstFalse || f1 == AigGraph::kConstFalse) {
    return AigGraph::kConstFalse;
  }
  if (f0 == AigGraph::kConstTrue) return f1;
  if (f1 == AigGraph::kConstTrue) return f0;
  if (f0 == f1) return f0;
  if (AigVar(f0) == AigVar(f1)) return AigGraph::kConstFalse;
  return orig;
}

static bool IsInputNode(const AigGraph& g, uint32_t id) {
  for (uint32_t inp : g.inputs) {
    if (inp == id) return true;
  }
  return false;
}

void ConstProp(AigGraph& g) {
  std::vector<uint32_t> remap(g.nodes.size() * 2);
  for (uint32_t i = 0; i < remap.size(); ++i) {
    remap[i] = i;
  }

  for (size_t i = 1; i < g.nodes.size(); ++i) {
    auto id = static_cast<uint32_t>(i);
    uint32_t lit = AigLit(id, false);
    if (IsInputNode(g, id)) continue;  // Skip primary inputs.
    auto& node = g.nodes[i];
    uint32_t f0 = remap[node.fanin0];
    uint32_t f1 = remap[node.fanin1];
    node.fanin0 = f0;
    node.fanin1 = f1;
    remap[lit] = SimplifyAnd(f0, f1, lit);
    remap[lit ^ 1u] = remap[lit] ^ 1u;
  }

  for (auto& out : g.outputs) {
    out = remap[out];
  }
  for (auto& [state_id, next] : g.latches) {
    next = remap[next];
  }
}

// =============================================================================
// AIG balancing
// =============================================================================

static void CollectAndLeaves(const AigGraph& g, uint32_t lit,
                             std::vector<uint32_t>& leaves) {
  if (IsConst(lit) || AigIsCompl(lit)) {
    leaves.push_back(lit);
    return;
  }
  uint32_t id = AigVar(lit);
  if (id == 0 || id >= g.nodes.size()) {
    leaves.push_back(lit);
    return;
  }
  const auto& node = g.nodes[id];
  if (node.fanin0 == 0 && node.fanin1 == 0) {
    leaves.push_back(lit);
    return;
  }
  CollectAndLeaves(g, node.fanin0, leaves);
  CollectAndLeaves(g, node.fanin1, leaves);
}

static uint32_t BuildBalancedAnd(AigGraph& g, std::vector<uint32_t>& leaves) {
  if (leaves.empty()) return AigGraph::kConstTrue;
  while (leaves.size() > 1) {
    std::vector<uint32_t> next;
    for (size_t i = 0; i + 1 < leaves.size(); i += 2) {
      next.push_back(g.AddAnd(leaves[i], leaves[i + 1]));
    }
    if (leaves.size() % 2 != 0) {
      next.push_back(leaves.back());
    }
    leaves = std::move(next);
  }
  return leaves[0];
}

void Balance(AigGraph& g) {
  for (auto& out : g.outputs) {
    if (IsConst(out) || AigIsCompl(out)) continue;
    std::vector<uint32_t> leaves;
    CollectAndLeaves(g, out, leaves);
    if (leaves.size() <= 2) continue;
    out = BuildBalancedAnd(g, leaves);
  }
}

// =============================================================================
// AIG rewriting (basic — delegates to ConstProp)
// =============================================================================

void Rewrite(AigGraph& g) { ConstProp(g); }

// =============================================================================
// AIG refactoring (basic — balance + constprop)
// =============================================================================

void Refactor(AigGraph& g) {
  Balance(g);
  ConstProp(g);
}

// =============================================================================
// Redundancy removal (basic — delegates to ConstProp)
// =============================================================================

void RemoveRedundancy(AigGraph& g) { ConstProp(g); }

}  // namespace delta
