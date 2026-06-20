

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Section 9.4.5 — intra-assignment timing controls. At the elaboration stage
// the only thing to confirm is that the intra-assignment delay, event, and
// repeat-event forms (applicable to both blocking and nonblocking assignments)
// elaborate cleanly into a design. The behavioural rules are observed at the
// simulation stage in test_simulator_clause_09_04_05.cpp.

TEST(IntraAssignTimingElaboration, BlockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a = #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, NonblockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a <= #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, BlockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, NonblockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, RepeatEventBlockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, RepeatEventNonblockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= repeat(5) @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
