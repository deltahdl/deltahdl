#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefElaboration, NochangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.6 Syntax 31-14: start_edge_offset and end_edge_offset are
// mintypmax_expression productions; elaboration must reduce a
// min:typ:max triple in each offset position without diagnostics.
TEST(TimingCheckEventDefElaboration, NochangeMinTypMaxOffsetsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.6: "The reference event can be specified with the posedge or
// negedge keyword." Both keyword forms must elaborate cleanly; this
// covers the negedge path.
TEST(TimingCheckEventDefElaboration, NochangeNegedgeReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(negedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.6 Syntax 31-14: the optional notifier trailing the two offsets
// resolves to a variable_identifier; elaboration must accept the form
// that binds an existing variable into that slot.
TEST(TimingCheckEventDefElaboration, NochangeWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg ntfr;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.6: negative offsets are explicitly allowed ("a negative offset
// for start edge shrinks the region" / "a negative offset for the end
// edge shrinks the region"). Elaboration must reduce a unary-minus
// expression in each offset position without diagnostics.
TEST(TimingCheckEventDefElaboration, NochangeNegativeOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, -2, -4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
