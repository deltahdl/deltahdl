// §29.4: Combinational UDPs

#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder &SetCombinational() {
    decl.is_sequential = false;
    return *this;
  }

  UdpBuilder &AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

TEST(UdpCombinational, AndGate) {
  UdpBuilder b;
  b.SetCombinational()
      .AddRow({'0', '0'}, '0')
      .AddRow({'0', '1'}, '0')
      .AddRow({'1', '0'}, '0')
      .AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

TEST(UdpCombinational, UnmatchedIsX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

}  // namespace
