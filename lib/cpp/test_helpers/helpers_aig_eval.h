#pragma once

#include <cstddef>
#include <cstdint>
#include <unordered_map>
#include <vector>

#include "synthesizer/aig.h"

using namespace delta;

// The value the outputs of `aig` carry when its inputs are driven with the bits
// of `inputs`: input i takes bit i of `inputs`, and output j lands in bit j of
// the result.
//
// A test that names the literal an output carries states the gates the lowering
// happened to build, so it fails when a lowering of the same function is wired
// differently and it says nothing about the function either way. Driving the
// inputs and reading the outputs states what the netlist computes, which is
// what a design is synthesized for.
//
// One pass in node order suffices: AigGraph::AddAnd allocates a node after the
// literals it is built from, so every fanin of node id is a literal over a node
// below id. Node 0 is the constant, whose value is false, which makes literal 0
// false and literal 1 true.
inline uint64_t EvalAigOutputs(const AigGraph& aig, uint64_t inputs) {
  std::vector<bool> value(aig.nodes.size(), false);
  std::unordered_map<uint32_t, size_t> input_bit;
  for (size_t i = 0; i < aig.inputs.size(); ++i) {
    input_bit[aig.inputs[i]] = i;
  }
  auto lit_value = [&value](uint32_t lit) {
    return value[AigVar(lit)] != AigIsCompl(lit);
  };
  for (uint32_t id = 1; id < aig.nodes.size(); ++id) {
    auto it = input_bit.find(id);
    if (it != input_bit.end()) {
      value[id] = ((inputs >> it->second) & 1u) != 0;
      continue;
    }
    const AigNode& node = aig.nodes[id];
    value[id] = lit_value(node.fanin0) && lit_value(node.fanin1);
  }
  uint64_t result = 0;
  for (size_t j = 0; j < aig.outputs.size(); ++j) {
    if (lit_value(aig.outputs[j])) {
      result |= uint64_t{1} << j;
    }
  }
  return result;
}
