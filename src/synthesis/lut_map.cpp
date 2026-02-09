#include "synthesis/lut_map.h"

#include <algorithm>
#include <cstdint>
#include <unordered_set>
#include <vector>

namespace delta {
namespace {

// Maximum number of cuts retained per node during enumeration.
constexpr uint32_t kMaxCutsPerNode = 8;

// =============================================================================
// Primary-input check
// =============================================================================

bool IsInput(const AigGraph& aig, uint32_t node_id) {
  for (uint32_t inp : aig.inputs) {
    if (inp == node_id) return true;
  }
  return false;
}

// =============================================================================
// Cut merging — combine two sets of cuts, filtering by max leaf count
// =============================================================================

std::vector<Cut> MergeCuts(const std::vector<Cut>& cuts0,
                           const std::vector<Cut>& cuts1, uint32_t max_k) {
  std::vector<Cut> result;
  for (const auto& c0 : cuts0) {
    for (const auto& c1 : cuts1) {
      std::unordered_set<uint32_t> merged(c0.leaves.begin(), c0.leaves.end());
      merged.insert(c1.leaves.begin(), c1.leaves.end());
      if (merged.size() > max_k) continue;
      Cut cut;
      cut.leaves.assign(merged.begin(), merged.end());
      std::sort(cut.leaves.begin(), cut.leaves.end());
      result.push_back(std::move(cut));
      if (result.size() >= kMaxCutsPerNode) return result;
    }
  }
  return result;
}

// =============================================================================
// Boolean evaluation — recursively evaluate a literal against leaf assignments
// =============================================================================

bool EvalNode(const AigGraph& aig, uint32_t lit,
              const std::vector<uint32_t>& leaf_ids, uint32_t assignment) {
  uint32_t node_id = AigVar(lit);
  bool compl_flag = AigIsCompl(lit);

  // Constant node.
  if (node_id == 0) return compl_flag;

  // Leaf in the cut — return its assigned value.
  for (size_t i = 0; i < leaf_ids.size(); ++i) {
    if (node_id != leaf_ids[i]) continue;
    bool val = ((assignment >> i) & 1u) != 0;
    return val ^ compl_flag;
  }

  // Recurse into AND gate.
  const auto& node = aig.nodes[node_id];
  bool val0 = EvalNode(aig, node.fanin0, leaf_ids, assignment);
  bool val1 = EvalNode(aig, node.fanin1, leaf_ids, assignment);
  return (val0 && val1) ^ compl_flag;
}

// =============================================================================
// Truth table computation
// =============================================================================

uint64_t ComputeTruthTable(const AigGraph& aig, uint32_t root_id,
                           const Cut& cut) {
  uint64_t tt = 0;
  uint32_t num_rows = 1u << static_cast<uint32_t>(cut.leaves.size());
  uint32_t root_lit = AigLit(root_id, false);
  for (uint32_t row = 0; row < num_rows; ++row) {
    if (EvalNode(aig, root_lit, cut.leaves, row)) {
      tt |= (uint64_t{1} << row);
    }
  }
  return tt;
}

// =============================================================================
// Best-cut selection — area-oriented: prefer fewest leaves
// =============================================================================

/// Select the best cut for covering. Skips trivial self-cuts (where the only
/// leaf is the root node itself) since those don't decompose logic.
const Cut* SelectBestCut(const std::vector<Cut>& cuts, uint32_t root_id) {
  const Cut* best = nullptr;
  for (const auto& cut : cuts) {
    bool is_self = (cut.leaves.size() == 1 && cut.leaves[0] == root_id);
    if (is_self) continue;
    if (best == nullptr || cut.leaves.size() < best->leaves.size()) {
      best = &cut;
    }
  }
  return best;
}

// =============================================================================
// Cut enumeration — bottom-up over all AIG nodes
// =============================================================================

void ProcessAndNode(const AigGraph& aig, uint32_t id, uint32_t lut_size,
                    std::vector<std::vector<Cut>>& all_cuts) {
  const auto& node = aig.nodes[id];
  uint32_t child0 = AigVar(node.fanin0);
  uint32_t child1 = AigVar(node.fanin1);

  auto merged = MergeCuts(all_cuts[child0], all_cuts[child1], lut_size);

  // Add the trivial cut: this node itself as a single leaf.
  Cut self_cut;
  self_cut.leaves.push_back(id);
  merged.push_back(std::move(self_cut));
  all_cuts[id] = std::move(merged);
}

std::vector<std::vector<Cut>> EnumerateCuts(const AigGraph& aig,
                                            uint32_t lut_size) {
  std::vector<std::vector<Cut>> all_cuts(aig.nodes.size());

  // Node 0 (constant): trivial cut with no leaves.
  all_cuts[0].push_back(Cut{});

  // Primary inputs: trivial cut is the input itself.
  for (uint32_t inp_id : aig.inputs) {
    Cut self_cut;
    self_cut.leaves.push_back(inp_id);
    all_cuts[inp_id].push_back(self_cut);
  }

  // AND nodes: merge fanin cuts (topological order guaranteed by node ids).
  for (size_t i = 1; i < aig.nodes.size(); ++i) {
    auto id = static_cast<uint32_t>(i);
    if (IsInput(aig, id)) continue;
    const auto& node = aig.nodes[i];
    if (node.fanin0 == 0 && node.fanin1 == 0) continue;
    ProcessAndNode(aig, id, lut_size, all_cuts);
  }
  return all_cuts;
}

// =============================================================================
// LUT cell construction
// =============================================================================

bool BuildTrivialCell(const AigGraph& aig, uint32_t out_lit,
                      LutMapping& mapping) {
  uint32_t node_id = AigVar(out_lit);
  bool is_compl = AigIsCompl(out_lit);

  // Constant output.
  if (node_id == 0) {
    LutCell cell;
    cell.output = node_id;
    cell.truth_table = is_compl ? 1u : 0u;
    mapping.cells.push_back(std::move(cell));
    return true;
  }

  // Direct wire from a primary input.
  if (!IsInput(aig, node_id)) return false;
  LutCell cell;
  cell.output = node_id;
  cell.inputs.push_back(node_id);
  // 1-input truth table: identity = 0b10, inversion = 0b01.
  cell.truth_table = is_compl ? 0b01u : 0b10u;
  mapping.cells.push_back(std::move(cell));
  return true;
}

void BuildOutputLut(const AigGraph& aig, uint32_t out_lit,
                    const std::vector<std::vector<Cut>>& all_cuts,
                    LutMapping& mapping) {
  uint32_t node_id = AigVar(out_lit);
  bool is_compl = AigIsCompl(out_lit);

  const auto& cuts = all_cuts[node_id];
  const Cut* best = SelectBestCut(cuts, node_id);
  if (best == nullptr) return;

  LutCell cell;
  cell.output = node_id;
  cell.inputs = best->leaves;
  cell.truth_table = ComputeTruthTable(aig, node_id, *best);

  // Apply output inversion by flipping all truth-table bits.
  if (is_compl) {
    uint32_t num_rows = 1u << static_cast<uint32_t>(best->leaves.size());
    cell.truth_table ^= (uint64_t{1} << num_rows) - 1u;
  }
  mapping.cells.push_back(std::move(cell));
}

void BuildCovering(const AigGraph& aig,
                   const std::vector<std::vector<Cut>>& all_cuts,
                   LutMapping& mapping) {
  for (uint32_t out_lit : aig.outputs) {
    if (BuildTrivialCell(aig, out_lit, mapping)) continue;
    BuildOutputLut(aig, out_lit, all_cuts, mapping);
  }
}

}  // namespace

// =============================================================================
// LutMapper public interface
// =============================================================================

LutMapper::LutMapper(uint32_t lut_size) : lut_size_(lut_size) {}

LutMapping LutMapper::Map(const AigGraph& aig) {
  LutMapping mapping;
  mapping.lut_size = lut_size_;

  if (aig.outputs.empty()) return mapping;

  auto all_cuts = EnumerateCuts(aig, lut_size_);
  BuildCovering(aig, all_cuts, mapping);
  return mapping;
}

}  // namespace delta
