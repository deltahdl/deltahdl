#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §25.6: when a port instance is an interface, each signal of the interface
// becomes an available specify terminal with the direction the modport
// restricts it to. A modport-input signal drives a module path source, so this
// must elaborate cleanly. Input is built from real interface (§25.3.2) and
// modport (§25.5) syntax so the direction actually comes from the modport.
TEST(SpecifyInterfaceTerminal, ModportInputUsableAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: a modport-output signal is available as a module path destination.
TEST(SpecifyInterfaceTerminal, ModportOutputUsableAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p);\n"
      "  specify\n"
      "    (i => p.b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: the modport restricts the terminal's direction, so a modport-output
// signal cannot serve as a module path source.
TEST(SpecifyInterfaceTerminal, ModportOutputRejectedAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.b => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: conversely, a modport-input signal cannot serve as a module path
// destination.
TEST(SpecifyInterfaceTerminal, ModportInputRejectedAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p);\n"
      "  specify\n"
      "    (i => p.a) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: a modport-inout signal is restricted to no single direction, so — like
// a module inout port — it is usable as both a source and a destination
// terminal. Exercises the inout branch of the modport-direction rule, distinct
// from the input-only and output-only branches above.
TEST(SpecifyInterfaceTerminal, ModportInoutUsableAsEitherDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic io;\n"
      "  modport mp(inout io);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.io => o) = 5;\n"
      "    (i => p.io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: an interface port with no modport carries the interface's default
// direction, which restricts nothing, so its signal is usable in either path
// role.
TEST(SpecifyInterfaceTerminal, PlainInterfaceSignalUsableEitherDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "endinterface\n"
      "module m(Bus p);\n"
      "  specify\n"
      "    (p.a => p.b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: an interface signal is equally available as a timing-check terminal,
// regardless of the modport direction.
TEST(SpecifyInterfaceTerminal, InterfaceSignalUsableAsTimingCheckTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, input clk);\n"
      "  specify\n"
      "    $setup(p.a, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: a ref port cannot be a terminal, and this extends to an interface
// signal reached through a ref modport member (path position).
TEST(SpecifyInterfaceTerminal, RefModportMemberRejectedAsPathTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(ref a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: the ref-modport-member prohibition applies to timing-check terminals
// too.
TEST(SpecifyInterfaceTerminal, RefModportMemberRejectedAsTimingTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(ref a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, input clk);\n"
      "  specify\n"
      "    $setup(p.a, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: module inout ports can act as either an input (source) or an output
// (destination) terminal, so both directions of use must elaborate cleanly.
TEST(SpecifyInoutTerminal, InoutPortUsableAsEitherTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, inout io, output o);\n"
      "  specify\n"
      "    (io => o) = 5;\n"
      "    (i => io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: a ref port cannot be used as a terminal in a specify block. Source
// position of a module path.
TEST(SpecifyRefTerminalRejected, RefPortRejectedAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(ref logic r, output o);\n"
      "  specify\n"
      "    (r => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: a ref port cannot be used as a terminal in a specify block.
// Destination position of a module path.
TEST(SpecifyRefTerminalRejected, RefPortRejectedAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, ref logic r);\n"
      "  specify\n"
      "    (i => r) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §25.6: a ref port cannot be used as a terminal in a specify block. Terminal
// of a timing check.
TEST(SpecifyRefTerminalRejected, RefPortRejectedAsTimingCheckTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(ref logic r, input clk);\n"
      "  specify\n"
      "    $setup(r, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
