#pragma once

#include <cstdint>
#include <vector>

namespace delta {

struct UdpDecl;

class UdpEvalState {
 public:
  explicit UdpEvalState(const UdpDecl& decl);
  // Seeds the output of a sequential primitive with `initial_output` -- '0',
  // '1' or 'x' -- in place of the bit UdpDecl::initial_value carries, for a
  // caller that has evaluated A.5.2's `output reg port_identifier =
  // constant_expression` where the parser could only keep it. A combinational
  // primitive's output starts at x whatever is passed, as under the other
  // constructor.
  UdpEvalState(const UdpDecl& decl, char initial_output);

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
