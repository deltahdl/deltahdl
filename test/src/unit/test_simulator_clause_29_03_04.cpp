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

// At simulation time, evaluating an input combination that no table row
// matches must produce x as the output.
TEST(UdpStateTable, CombinationalEvaluationOfUnspecifiedCombinationYieldsX) {
  auto decl = MakeCombinational({{'0', '0'}, {'1', '1'}}, {'0', '1'});
  UdpEvalState state(decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

// The default-x behavior holds for every unspecified combination, not just a
// single case.
TEST(UdpStateTable, CombinationalEveryUnspecifiedCombinationYieldsX) {
  auto decl = MakeCombinational({{'0', '0'}}, {'0'});
  UdpEvalState state(decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '1'}), 'x');
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

// Specified rows continue to match after unspecified rows are queried — the
// default-x behavior does not overwrite the table.
TEST(UdpStateTable, SpecifiedRowsStillMatchAfterUnspecifiedQuery) {
  auto decl = MakeCombinational({{'0', '0'}, {'1', '1'}}, {'0', '1'});
  UdpEvalState state(decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

}  // namespace
