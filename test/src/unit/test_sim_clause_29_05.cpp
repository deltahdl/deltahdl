// §29.5: Level-sensitive sequential UDPs

#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder& SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }

  UdpBuilder& AddSeqRow(std::vector<char> inputs, char state, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.current_state = state;
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

TEST(UdpLevelSeq, Latch) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0', '?'}, '?', '-')
      .AddSeqRow({'1', '0'}, '?', '0')
      .AddSeqRow({'1', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'1', '0'});
  EXPECT_EQ(state.GetOutput(), '0');
}

TEST(UdpLevelSeq, NoChange) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0'}, '?', '-')
      .AddSeqRow({'1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
