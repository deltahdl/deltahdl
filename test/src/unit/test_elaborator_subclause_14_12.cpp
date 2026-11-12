#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DefaultClockingElab, DuplicateDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk1, clk2;\n"
      "  logic a; default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  logic b; default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            5, "14.12"));
}

TEST(DefaultClockingElab, AssignExistingClockingBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultClockingElab, AssignUnknownClockingBlockErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"cb\" does not name a clocking "
                            "block",
                            2, "14.12"));
}

TEST(DefaultClockingElab, AssignNonClockingEntityErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic cb;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"cb\" does not name a clocking "
                            "block",
                            3, "14.12"));
}

TEST(DefaultClockingElab, SingleDefaultClockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultClockingElab, DuplicateDefaultClockingViaAssignmentErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            8, "14.12"));
}

TEST(DefaultClockingElab, DuplicateDefaultViaMixedInlineAndAssignmentErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            7, "14.12"));
}

TEST(DefaultClockingElab, NestedModuleNamesEnclosingClockingBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module processor;\n"
             "  logic clk1;\n"
             "  clocking busA @(posedge clk1); endclocking\n"
             "  module cpu;\n"
             "    default clocking busA;\n"
             "    initial ##5 $display(\"x\");\n"
             "  endmodule\n"
             "  module bad;\n"
             "    default clocking nosuch;\n"
             "  endmodule\n"
             "  cpu u();\n"
             "  bad b();\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "default clocking \"busA\" does not name", 5,
                             "14.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"nosuch\" does not name", 9,
                            "14.12"));
}

const char* const kDefaultScopes[] = {"interface", "program", "checker"};

static std::string ScopeWithDefaults(const std::string& kind,
                                     const std::string& first,
                                     const std::string& second) {
  return kind + " s(input logic clk);\n" +
         "  clocking c1 @(posedge clk); endclocking\n"
         "  clocking c2 @(negedge clk); endclocking\n"
         "  " +
         first + "\n  " + second + "\nend" + kind +
         "\n"
         "module top; logic clk; s u(clk); endmodule\n";
}

static void ExpectSecondDefaultReported(const std::string& first,
                                        const std::string& second) {
  for (const char* kind : kDefaultScopes) {
    SCOPED_TRACE(kind);
    ElabFixture f;
    auto* design =
        ElaborateSrc(ScopeWithDefaults(kind, first, second), f, "top");
    ASSERT_NE(design, nullptr);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "only one default clocking block is allowed per "
                              "scope",
                              5, "14.12"));
  }
}

TEST(DefaultClockingElab, SecondInlineDefaultInEachScopeIsReported) {
  ExpectSecondDefaultReported(
      "default clocking d1 @(posedge clk); endclocking",
      "default clocking d2 @(negedge clk); endclocking");
}

TEST(DefaultClockingElab, InlineThenNamedDefaultInEachScopeIsReported) {
  ExpectSecondDefaultReported("default clocking d1 @(posedge clk); endclocking",
                              "default clocking c1;");
}

TEST(DefaultClockingElab, TwoNamedDefaultsInEachScopeAreReported) {
  ExpectSecondDefaultReported("default clocking c1;", "default clocking c2;");
}

TEST(DefaultClockingElab, OneDefaultInEachScopeIsAccepted) {
  for (const char* kind : kDefaultScopes) {
    for (const char* only : {"default clocking d1 @(posedge clk); endclocking",
                             "default clocking c1;"}) {
      SCOPED_TRACE(std::string(kind) + ": " + only);
      ElabFixture f;
      auto* design = ElaborateSrc(ScopeWithDefaults(kind, only, ""), f, "top");
      ASSERT_NE(design, nullptr);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(DefaultClockingElab, DefaultsInDifferentElementsAreAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface i(input logic clk);\n"
      "  default clocking di @(posedge clk); endclocking\n"
      "endinterface\n"
      "program p(input logic clk);\n"
      "  default clocking dp @(posedge clk); endclocking\n"
      "endprogram\n"
      "checker c(input logic clk);\n"
      "  default clocking dc @(posedge clk); endclocking\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  default clocking dt @(posedge clk); endclocking\n"
      "  module inner;\n"
      "    default clocking dn @(negedge clk); endclocking\n"
      "  endmodule\n"
      "  inner n();\n"
      "  i ui(clk);\n"
      "  p up(clk);\n"
      "  c uc(clk);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultClockingElab,
     AnInstantiatedModuleOrInterfaceDoesNotTakeTheDefault) {
  for (const char* kind : {"module", "interface"}) {
    SCOPED_TRACE(kind);
    ElabFixture f;
    auto* design = ElaborateSrc(std::string(kind) +
                                    " inner;\n"
                                    "  initial ##2 $display(\"x\");\n"
                                    "end" +
                                    kind +
                                    "\n"
                                    "module top;\n"
                                    "  logic clk;\n"
                                    "  default clocking cb @(posedge clk); "
                                    "endclocking\n"
                                    "  inner u();\n"
                                    "endmodule\n",
                                f, "top");
    ASSERT_NE(design, nullptr);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "cycle delay (##) requires a default clocking block", 2, "14.11"));
  }
}

}  // namespace
