#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

// Clause 29.2 (Overview) carries a single normative requirement: a z value
// presented on a UDP input is treated exactly as if it were an x value. These
// tests observe the production coercion (UdpEvalState's CoerceUdpInput) being
// applied on both the level-sensitive (Evaluate) and edge-sensitive
// (EvaluateWithEdge) evaluation paths.

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetCombinational() {
    decl.is_sequential = false;
    return *this;
  }

  UdpBuilder& SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder& AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

// Level path: an x-symbol row matches a z-driven input. Without coercion the z
// would match no row and Evaluate would fall through to the default x; the
// shall is observed because z yields the same '1' the x row produces.
TEST(UdpInputHighImpedanceTreatedAsX, ZInputTreatedAsXInLevelEvaluation) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'x'}, '1').AddRow({'0'}, '0');

  UdpEvalState with_z(b.decl);
  UdpEvalState with_x(b.decl);
  EXPECT_EQ(with_z.Evaluate({'z'}), '1');
  EXPECT_EQ(with_x.Evaluate({'x'}), '1');

  // Control: a genuinely distinct level still selects its own row.
  UdpEvalState with_zero(b.decl);
  EXPECT_EQ(with_zero.Evaluate({'0'}), '0');
}

// Edge path: the previous value handed to EvaluateWithEdge is coerced. A 'p'
// edge admits an x->1 transition, so a z previous value (coerced to x) must
// match it identically to an x previous value.
TEST(UdpInputHighImpedanceTreatedAsX, ZPreviousValueTreatedAsXInEdgeEvaluation) {
  UdpBuilder b;
  b.SetSequential().AddRow({'p'}, '1');

  UdpEvalState from_z(b.decl);
  UdpEvalState from_x(b.decl);
  EXPECT_EQ(from_z.EvaluateWithEdge({'1'}, 0, 'z'), '1');
  EXPECT_EQ(from_x.EvaluateWithEdge({'1'}, 0, 'x'), '1');
}

// Edge path: a z on a steady (level) input within an edge row is coerced, so
// the '?' level symbol matches it just as it would match an x.
TEST(UdpInputHighImpedanceTreatedAsX, ZLevelInputTreatedAsXInEdgeEvaluation) {
  UdpBuilder b;
  b.SetSequential().AddRow({'r', '?'}, '1');

  UdpEvalState with_z(b.decl);
  UdpEvalState with_x(b.decl);
  EXPECT_EQ(with_z.EvaluateWithEdge({'1', 'z'}, 0, '0'), '1');
  EXPECT_EQ(with_x.EvaluateWithEdge({'1', 'x'}, 0, '0'), '1');
}

}
