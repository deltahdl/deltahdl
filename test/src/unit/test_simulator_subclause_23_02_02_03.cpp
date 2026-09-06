#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §23.2.2.3 decides whether a port is a net or a variable: "an implicit data
// type declaration implies a net unless the var keyword is used", an input or
// inout with no port kind "shall default to a net of default net type", and an
// output with no port kind is a net where its data type is omitted or implicit
// and a variable where an explicit data type is given. A ref port is always a
// variable.
//
// A port the clause makes a net is a net, and everything a net carries applies
// to it: §28.12 resolves its drivers against each other, and the strength that
// resolution produces is what %v (§21.2.1.4) reports. These cases observe that
// through the running model rather than through the elaborated port record,
// because it is the model that was missing a net -- the elaborator has decided
// the kind correctly all along.
TEST(PortKindSimulation, HeaderOutputPortResolvesItsDriversAgainstEachOther) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t(output o);\n"
      "  assign o = 1'b1;\n"
      "  assign o = 1'b0;\n"
      "endmodule\n",
      f, "o");
  ASSERT_NE(var, nullptr);
  // §28.12: two drivers of equal strength and opposite value resolve to x. A
  // port that is no net has no second driver to resolve against, so whichever
  // assignment wrote last stands, and the answer is a definite 0 or 1.
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// The same source with the port declared in the body instead. §23.2.2.3 makes
// the header spelling a net of the default net type, so the two must agree --
// the claim is that where the port is written decides nothing, not that one of
// the two spellings happens to work.
TEST(PortKindSimulation, BodyWireSpellingResolvesTheSameWay) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t(o);\n"
      "  output o;\n"
      "  wire o;\n"
      "  assign o = 1'b1;\n"
      "  assign o = 1'b0;\n"
      "endmodule\n",
      f, "o");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// §21.2.1.4 reports the strength of a net, and a header port that is one has a
// strength to report: a (pull0, pull1) assignment drives it at pull, which
// renders Pu1. A port that is no net answers no strength at all, which %v
// renders as the empty string.
TEST(PortKindSimulation, HeaderOutputPortReportsItsDriversStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module t(output o);\n"
      "  assign (pull0, pull1) o = 1'b1;\n"
      "  initial #1 $display(\"[%v]\", o);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Pu1"), std::string::npos) << out;
}

// §23.2.2.3: an output whose data type is given explicitly is a variable, not a
// net -- `output integer x` is a var where `output x` and `output signed [5:0]
// x` are wires. So the change is about which ports become nets rather than all
// of them, and a variable port still answers no net.
TEST(PortKindSimulation, HeaderOutputWithExplicitDataTypeIsNoNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(output integer o);\n"
      "  initial o = 32'd7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindNet("o"), nullptr);
  auto* var = f.ctx.FindVariable("o");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §23.2.2.3: an input with no port kind is a net of default net type whatever
// its data type -- `input x` and `input integer x` are both wires -- so the
// input direction reaches the same model the output cases above do.
TEST(PortKindSimulation, HeaderInputPortIsANet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_NE(f.ctx.FindNet("i"), nullptr);
}

}  // namespace
