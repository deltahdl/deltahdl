#pragma once

#include <cstdint>
#include <vector>

namespace delta {

struct UdpDecl;

class UdpEvalState {
 public:
  explicit UdpEvalState(const UdpDecl& decl);

  char Evaluate(const std::vector<char>& inputs);

  char EvaluateWithEdge(const std::vector<char>& new_inputs,
                        uint32_t changed_idx, char prev_value);

  void SetInputs(const std::vector<char>& inputs);

  char GetOutput() const { return output_; }

 private:
  const UdpDecl& decl_;
  char output_;
  std::vector<char> prev_inputs_;
};

}  // namespace delta
