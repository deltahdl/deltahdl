#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecparamElaboration, SpecparamReferencedByParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  parameter p = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tRISE") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, LocalparamReferencingSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamNotInParameterList) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tRISE = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    EXPECT_NE(p.name, "tRISE");
  }
}

TEST(SpecparamElaboration, SpecparamReferencingPriorSpecparamSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tBase = 10;\n"
      "  specparam tDerived = tBase + 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecparamElaboration, SpecparamOutsideSpecifyCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tPD = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tPD") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, AssignmentToSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  initial delay = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'delay'", 3, "6.20"));
}

TEST(SpecparamElaboration, NonblockingAssignmentToSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  initial delay <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'delay'", 3, "6.20"));
}

TEST(SpecparamElaboration, SpecparamInDeclarationRangeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam width = 8;\n"
      "  logic [width-1:0] data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "specparam 'width' may not appear in a declaration "
                            "range specification",
                            3, "6.20.5"));
}

TEST(SpecparamElaboration, ParameterInDeclarationRangeSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  parameter width = 8;\n"
      "  logic [width-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecparamElaboration, SpecparamRangeWidthFromDeclaration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam [7:0] tDELAY = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tDELAY") {
      found = true;
      EXPECT_EQ(v.width, 8u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamNoRangeDefaultsToFinalValueWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tPD = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tPD") {
      found = true;
      EXPECT_EQ(v.width, 32u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamNoRangeTakesSizedLiteralWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tW = 4'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tW") {
      found = true;
      EXPECT_EQ(v.width, 4u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamAssignedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  specparam tX = P + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tX") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamAssignedFromLocalparamSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam L = 4;\n"
      "  specparam tX = L + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tX") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamInAParameterConditionalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = delay ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamInAParameterCallArgumentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  localparam lp = f(delay);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 4,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamInAParameterConcatenationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = {delay, 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamAsAParameterReplicationCountIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = {delay{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamAsAParameterIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  logic [63:0] arr;\n"
      "  localparam lp = arr[delay];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 4,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamInADeclarationRangeCallIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam width = 8;\n"
      "  function int f(int a); return a; endfunction\n"
      "  logic [f(width)-1:0] data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "specparam 'width' may not appear in a declaration "
                            "range specification",
                            4, "6.20.5"));
}

TEST(SpecparamElaboration, ParameterInAConditionalStillSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  parameter width = 8;\n"
      "  localparam lp = width ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
