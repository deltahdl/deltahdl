#include <gtest/gtest.h>

#include <vector>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

UdpDecl MakeCombinational(std::vector<std::vector<char>> rows,
                         std::vector<char> outputs) {
  UdpDecl decl;
  for (size_t i = 0; i < rows.size(); ++i) {
    UdpTableRow row;
    row.inputs = std::move(rows[i]);
    row.output = outputs[i];
    decl.table.push_back(row);
  }
  return decl;
}

// An explicitly specified all-x input row drives the output to x, consistent
// with the all-x-inputs rule that also forces an x output.
TEST(UdpStateTable, CombinationalExplicitAllXRowProducesX) {
  auto decl = MakeCombinational(
      {{'0', '0'}, {'1', '1'}, {'x', 'x'}},
      {'0', '1', 'x'});
  UdpEvalState state(decl);
  EXPECT_EQ(state.Evaluate({'x', 'x'}), 'x');
}

}  // namespace
