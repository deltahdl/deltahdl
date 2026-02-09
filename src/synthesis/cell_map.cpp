#include "synthesis/cell_map.h"

#include <cstdint>
#include <string>
#include <vector>

#include "synthesis/aig.h"
#include "synthesis/liberty.h"

namespace delta {
namespace {

// =============================================================================
// Net naming helpers
// =============================================================================

std::string InputNetName(const AigGraph& aig, uint32_t lit) {
  uint32_t node_id = AigVar(lit);
  bool compl_flag = AigIsCompl(lit);
  if (node_id == 0) return compl_flag ? "const1" : "const0";
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    if (aig.inputs[i] == node_id) {
      std::string name = "i" + std::to_string(i);
      return compl_flag ? "~" + name : name;
    }
  }
  std::string name = "n" + std::to_string(node_id);
  return compl_flag ? "~" + name : name;
}

std::string OutputNetName(const AigGraph& aig, uint32_t lit, size_t idx) {
  uint32_t node_id = AigVar(lit);
  if (node_id == 0) return "o" + std::to_string(idx);
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    if (aig.inputs[i] == node_id) return "o" + std::to_string(idx);
  }
  return "n" + std::to_string(node_id);
}

// =============================================================================
// Pattern classification for AIG subgraphs
// =============================================================================

enum class GateKind : uint8_t {
  kAnd,
  kOr,
  kInv,
  kBuf,
  kConst,
  kUnknown,
};

struct GatePattern {
  GateKind kind = GateKind::kUnknown;
  std::vector<uint32_t> input_lits;  // AIG literals for gate inputs
};

/// Classify the logic driving a single output literal.
GatePattern ClassifyOutput(const AigGraph& aig, uint32_t out_lit) {
  uint32_t node_id = AigVar(out_lit);
  bool compl_flag = AigIsCompl(out_lit);

  // Constant output.
  if (node_id == 0) return {GateKind::kConst, {}};

  // Primary input -- buffer or inverter.
  for (uint32_t inp : aig.inputs) {
    if (inp != node_id) continue;
    if (compl_flag) return {GateKind::kInv, {AigLit(node_id, false)}};
    return {GateKind::kBuf, {AigLit(node_id, false)}};
  }

  const auto& node = aig.nodes[node_id];

  // Complemented AND node -> check for OR pattern (De Morgan).
  // ~(~a & ~b) = a | b
  if (compl_flag && AigIsCompl(node.fanin0) && AigIsCompl(node.fanin1)) {
    uint32_t a = AigLit(AigVar(node.fanin0), false);
    uint32_t b = AigLit(AigVar(node.fanin1), false);
    return {GateKind::kOr, {a, b}};
  }

  // Non-complemented AND node.
  if (!compl_flag) {
    return {GateKind::kAnd, {node.fanin0, node.fanin1}};
  }

  return {GateKind::kUnknown, {}};
}

// =============================================================================
// Function string matching -- find a Liberty cell matching a gate pattern
// =============================================================================

/// Normalize a function pattern to a canonical gate kind.
GateKind ClassifyFunction(const std::string& func) {
  if (func == "!A" || func == "A'") return GateKind::kInv;
  if (func == "A") return GateKind::kBuf;
  if (func == "A * B" || func == "A&B" || func == "A & B") {
    return GateKind::kAnd;
  }
  if (func == "A + B" || func == "A|B" || func == "A | B") {
    return GateKind::kOr;
  }
  return GateKind::kUnknown;
}

const LibCell* FindCell(const Liberty& lib, GateKind kind) {
  for (const auto& cell : lib.cells) {
    for (const auto& pin : cell.pins) {
      if (pin.direction != "output") continue;
      if (ClassifyFunction(pin.function) == kind) return &cell;
    }
  }
  return nullptr;
}

// =============================================================================
// Fallback decomposition for unrecognized patterns
// =============================================================================

void MapFallback(const AigGraph& aig, const Liberty& lib, uint32_t out_lit,
                 size_t out_idx, CellMapping& result) {
  uint32_t node_id = AigVar(out_lit);
  // Cannot decompose constants or primary inputs further.
  if (node_id == 0) return;
  for (uint32_t inp : aig.inputs) {
    if (inp == node_id) return;
  }
  bool compl_flag = AigIsCompl(out_lit);
  const auto& node = aig.nodes[node_id];

  // Map the AND gate.
  const LibCell* and_cell = FindCell(lib, GateKind::kAnd);
  if (and_cell != nullptr) {
    CellInstance inst;
    inst.cell_name = and_cell->name;
    inst.output_net = "n" + std::to_string(node_id);
    inst.input_nets.push_back(InputNetName(aig, node.fanin0));
    inst.input_nets.push_back(InputNetName(aig, node.fanin1));
    result.instances.push_back(std::move(inst));
  }

  // Add inverter if the output is complemented.
  if (!compl_flag) return;
  const LibCell* inv_cell = FindCell(lib, GateKind::kInv);
  if (inv_cell == nullptr) return;
  CellInstance inst;
  inst.cell_name = inv_cell->name;
  inst.output_net = OutputNetName(aig, out_lit, out_idx);
  inst.input_nets.push_back("n" + std::to_string(node_id));
  result.instances.push_back(std::move(inst));
}

// =============================================================================
// Single-output mapping
// =============================================================================

void MapOutput(const AigGraph& aig, const Liberty& lib, uint32_t out_lit,
               size_t out_idx, CellMapping& result) {
  GatePattern pat = ClassifyOutput(aig, out_lit);
  const LibCell* cell = FindCell(lib, pat.kind);
  if (cell == nullptr) {
    MapFallback(aig, lib, out_lit, out_idx, result);
    return;
  }

  CellInstance inst;
  inst.cell_name = cell->name;
  inst.output_net = OutputNetName(aig, out_lit, out_idx);
  for (uint32_t lit : pat.input_lits) {
    inst.input_nets.push_back(InputNetName(aig, lit));
  }
  result.instances.push_back(std::move(inst));
}

}  // namespace

// =============================================================================
// CellMapper public interface
// =============================================================================

CellMapper::CellMapper(const Liberty& lib) : lib_(lib) {}

CellMapping CellMapper::Map(const AigGraph& aig) const {
  CellMapping mapping;
  for (size_t i = 0; i < aig.outputs.size(); ++i) {
    MapOutput(aig, lib_, aig.outputs[i], i, mapping);
  }
  return mapping;
}

}  // namespace delta
