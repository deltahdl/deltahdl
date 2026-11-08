#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssertionStatementElaboration, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration,
     AClockingEventWithoutAnEdgeDrawsNoAlwaysFfWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clkev, a;\n"
      "  assert property (@(clkev) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AssertionStatementElaboration, AssertPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssertPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, CoverPropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssumePropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration,
     RestrictPropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssumePropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssumePropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, CoverPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, CoverPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, RestrictPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, RestrictPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration,
     AlwaysAssertPropertyEquivalentFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration,
     AlwaysCoverPropertyEquivalentFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
