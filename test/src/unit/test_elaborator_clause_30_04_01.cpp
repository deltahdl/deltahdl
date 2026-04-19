#include "fixture_elaborator.h"

using namespace delta;

namespace {

// An input port is the baseline source form: the source rule permits a net
// connected to an input or inout port.
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

// An inout port may serve as the source of a module path because the source
// rule permits a net connected to an input or inout port.
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

// An output port is the baseline destination form permitted by the
// destination rule.
TEST(SpecifyTerminalElaboration, OutputPortAsDestinationElaborates) {
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

// An inout port may serve as the destination of a module path because the
// destination rule permits a net or variable connected to an output or inout
// port.
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

// The destination rule explicitly permits a variable (not only a net) when
// that variable is connected to an output port.
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

// An output port cannot be the source of a module path: the source rule
// restricts sources to input or inout ports.
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

// An input port cannot be the destination of a module path: the destination
// rule restricts destinations to output or inout ports.
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

// A ref port is neither input/inout (source rule) nor output/inout
// (destination rule), so it cannot be used as a module path terminal.
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

// A source identifier that is not connected to any module port violates the
// source rule's "connected to a module input port or inout port" clause.
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

// A destination identifier that is not connected to any module port violates
// the destination rule's "connected to an output or inout port" clause.
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

// A variable cannot be the source of a module path: the source rule requires
// the source to be a net.
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

}  // namespace
