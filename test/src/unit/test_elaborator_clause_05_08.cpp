#include "fixture_elaborator.h"

namespace {

TEST(TimeLiteralElaboration, AllSixUnitsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    #1fs;\n"
             "    #1ps;\n"
             "    #1ns;\n"
             "    #1us;\n"
             "    #1ms;\n"
             "    #1s;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TimeLiteralElaboration, TimeLiteralInAssignmentElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  realtime r;\n"
             "  initial r = 5ns;\n"
             "endmodule\n"));
}

// §5.8: a time literal is interpreted as a realtime value scaled to the current
// time unit. When such a literal initializes an integer-typed parameter the
// elaborator must const-evaluate it through the real path, so 3000ps under the
// default ns unit scales to 3.0 and rounds to 3 (not the raw magnitude 3000).
TEST(TimeLiteralElaboration, TimeLiteralConstFoldsIntoIntegerParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

// §5.8, constant-expression form via a module `parameter` (as opposed to the
// `localparam` above): a parameter's default value takes a distinct resolution
// path, but the time literal must still be interpreted as its scaled realtime
// value, so 3000ps under the default ns unit const-folds to 3.
TEST(TimeLiteralElaboration, TimeLiteralConstFoldsIntoParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

// §5.8 + §3.14: the same literal scales to whatever the current time unit is.
// With an explicit `timeunit 1ps` the literal 3000ps is already in the current
// unit, so it const-folds to 3000 rather than the ns-scaled 3.
TEST(TimeLiteralElaboration, TimeLiteralConstFoldScalesToCurrentUnit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  timeunit 1ps;\n"
      "  localparam int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3000);
}

}  // namespace
