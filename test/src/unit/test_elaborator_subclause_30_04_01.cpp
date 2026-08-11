#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyTerminalElaboration, InputPortAsSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAsInputTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(inout io, output o);\n"
      "  specify\n"
      "    (io => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAsOutputTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, inout io);\n"
      "  specify\n"
      "    (i => io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, VariableAsDestinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, output reg o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, OutputPortAsSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, output o);\n"
      "  specify\n"
      "    (o => i) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InputPortAsDestinationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i1, input i2);\n"
      "  specify\n"
      "    (i1 => i2) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, RefPortAsTerminalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(ref logic r, output o);\n"
      "  specify\n"
      "    (r => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, RefPortAsDestinationErrors) {
  // C2: the destination must be connected to an output or inout port; a ref
  // port is neither, so it is rejected on the destination side of the path.
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, ref logic r);\n"
      "  specify\n"
      "    (i => r) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, UnconnectedSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output o);\n"
      "  wire local_net;\n"
      "  specify\n"
      "    (local_net => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, UnconnectedDestinationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i);\n"
      "  wire local_net;\n"
      "  specify\n"
      "    (i => local_net) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, VariableAsSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input var logic i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.1: the report that refuses a variable module path source names the
// subclause stating the rule ("The module path source shall be a net that is
// connected to a module input port or inout port").
TEST(SpecifyTerminalElaboration, VariableSourceNames30_4_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input var logic i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag = FindDiag(f, "must be a net");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "30.4.1");
}

}  // namespace
