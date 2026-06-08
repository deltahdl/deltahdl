#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §25.6: when a port instance is an interface, each signal of the interface is
// available as a specify-block terminal. Interface-qualified terminals must
// elaborate without complaint in source and destination positions of a path.
TEST(SpecifyInterfaceTerminal, InterfaceSignalUsableAsPathTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (intf.sig => intf.out) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §25.6: an interface signal is equally available as a timing-check terminal.
TEST(SpecifyInterfaceTerminal, InterfaceSignalUsableAsTimingCheckTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(intf.data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

}
