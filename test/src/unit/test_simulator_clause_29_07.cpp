#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

// §29.7 Sequential UDP initialization (simulation-start semantics).
//
// The initial statement of a sequential UDP sets the output's value at the
// start of simulation, and that value becomes the current state in the state
// table. The instance delay on an instantiated UDP does not delay this
// assignment: the value is applied immediately. UdpEvalState's constructor in
// src/simulator/udp_eval.cpp carries this — it seeds output_ from the recorded
// initial value (with no delay parameter), and that seeded value then drives
// row selection through MatchState on the next evaluation.

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
};

// The initial statement is optional: with none, a sequential UDP starts in the
// unknown state rather than taking a specified start value.
TEST(UdpInitialStatement, DefaultIsX) {
  UdpBuilder b;
  b.SetSequential();

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), 'x');
}

// The specified initial value is the output at the start of simulation and
// serves as the current state in the state table: with the same input, the
// only difference between the two runs is the initial value, and it alone
// selects which current-state row matches.
TEST(UdpInitialStatement, InitialValueServesAsCurrentState) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  // Two rows share the same input level but discriminate on current state:
  //   in=0, state=1 -> 1   (hold high)
  //   in=0, state=0 -> 0   (hold low)
  decl.table.push_back(UdpTableRow{/*inputs=*/{'0'}, /*paren_edges=*/{},
                                   /*current_state=*/'1', /*output=*/'1'});
  decl.table.push_back(UdpTableRow{/*inputs=*/{'0'}, /*paren_edges=*/{},
                                   /*current_state=*/'0', /*output=*/'0'});

  decl.initial_value = '1';
  UdpEvalState high(decl);
  EXPECT_EQ(high.GetOutput(), '1');
  EXPECT_EQ(high.Evaluate({'0'}), '1');

  decl.initial_value = '0';
  UdpEvalState low(decl);
  EXPECT_EQ(low.GetOutput(), '0');
  EXPECT_EQ(low.Evaluate({'0'}), '0');
}

}  // namespace
