#pragma once

#include <cstdint>
#include <vector>

namespace delta {

struct UdpDecl;

// §29: Runtime evaluator for user-defined primitive tables.
// Handles combinational and sequential (level/edge-sensitive) UDPs,
// including §29.10 level-sensitive dominance.
class UdpEvalState {
 public:
  explicit UdpEvalState(const UdpDecl& decl);

  // Combinational evaluate: given input levels, return output.
  char Evaluate(const std::vector<char>& inputs);

  // Sequential evaluate with edge info: new inputs, which input changed,
  // and its previous value. Returns the new output.
  char EvaluateWithEdge(const std::vector<char>& new_inputs,
                        uint32_t changed_idx, char prev_value);

  // Set current input values (for tracking previous state).
  void SetInputs(const std::vector<char>& inputs);

  // Get current output (state for sequential, last result for combinational).
  char GetOutput() const { return output_; }

 private:
  const UdpDecl& decl_;
  char output_;
  std::vector<char> prev_inputs_;
};

}  // namespace delta
