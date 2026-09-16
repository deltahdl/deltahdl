#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// §16.13: the process of an assertion whose sequence names a clock of its
// own wakes on that clock beside the leading one, and the statement keeps
// the leading clock alone, on which every attempt begins.
TEST(MulticlockElaboration, TheProcessWakesOnEveryClockTheSequenceNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk0, clk1, sig0, sig1;\n"
      "  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = nullptr;
  for (const auto& candidate : design->top_modules[0]->processes) {
    if (candidate.kind == RtlirProcessKind::kAlwaysFF) p = &candidate;
  }
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 2u);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk0");
  EXPECT_EQ(p->sensitivity[1].signal->text, "clk1");
  EXPECT_EQ(p->sensitivity[1].edge, Edge::kPosedge);
  ASSERT_NE(p->body, nullptr);
  ASSERT_EQ(p->body->assert_clock.size(), 1u);
  EXPECT_EQ(p->body->assert_clock[0].signal->text, "clk0");
}

}  // namespace
