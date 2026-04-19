#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.8: the LRM's worked example uses an 8-bit data terminal `DAT`
// against a scalar clock. The bare-vector form (no part-select) must
// elaborate cleanly so the §31.8 default semantics apply.
TEST(VectorSignalsInTimingChecks, BareVectorDataTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] DAT;\n"
      "  logic CLK;\n"
      "  specify\n"
      "    $setup(DAT, posedge CLK, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.8: "Either or both signals" — a vector reference event paired
// with a vector data terminal exercises the both-vector arm of the
// rule and must elaborate without diagnostics.
TEST(VectorSignalsInTimingChecks, BothVectorTerminalsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic [1:0] clk;\n"
      "  specify\n"
      "    $hold(posedge clk[1:0], data[7:0], 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.8: the plus-indexed part-select form is one of the four vector
// terminal grammars and must elaborate as cleanly as the simple
// part-select form.
TEST(VectorSignalsInTimingChecks, PlusIndexedVectorTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  specify\n"
      "    $setup(data[0+:8], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.8: a single-signal check ($width) accepts a vector reference
// terminal. Even though the data event is derived from the same signal,
// the vector form must still survive elaboration.
TEST(VectorSignalsInTimingChecks, WidthVectorReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] rst;\n"
      "  specify\n"
      "    $width(posedge rst[3:0], 20);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.8: $period is the second single-signal check the LRM enumerates.
// A vector reference terminal must elaborate here as well.
TEST(VectorSignalsInTimingChecks, PeriodVectorReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] clk;\n"
      "  specify\n"
      "    $period(posedge clk[1:0], 100);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.8: $nochange is the last two-signal check the LRM lists. A
// vector data terminal here must elaborate without errors so the
// default vector semantics carry into runtime construction.
TEST(VectorSignalsInTimingChecks, NochangeVectorDataElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $nochange(posedge clk, data[7:0], 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
