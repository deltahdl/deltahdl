#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"

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

struct SpecparamUse {
  const char* where;
  bool instantiates_child;
  const char* src;
  const char* message;
  uint32_t line;
  const char* subclause;
};

constexpr const char* kChild =
    "module c #(parameter int P = 1);\n  specparam sp = 1;\nendmodule\n";

TEST(SpecparamElaboration, ParameterValueNamingASpecparamIsReportedEverywhere) {
  const SpecparamUse kUses[] = {
      {"real specparam in the clause's RAM16GEN example", false,
       "module ram16gen;\n  specparam dhold = 1.0;\n  specparam ddly = 1.0;\n"
       "  parameter width = 1;\n  parameter regsize = dhold + 1.0;\n"
       "endmodule\n",
       "parameter references specparam 'dhold'", 5, "6.20.5"},
      {"parameter in an if-generate block", false,
       "module m;\n  specparam sp = 2;\n  if (1) begin : g\n"
       "    parameter int p = sp;\n  end\nendmodule\n",
       "parameter references specparam 'sp'", 4, "6.20.5"},
      {"localparam in an else-generate block", false,
       "module m;\n  specparam sp = 2;\n  if (0) begin : g\n"
       "  end else begin : h\n    localparam int p = sp + 1;\n  end\n"
       "endmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"localparam in a case-generate arm", false,
       "module m;\n  specparam sp = 2;\n  case (1)\n    1: begin : g\n"
       "      localparam int p = sp;\n    end\n  endcase\nendmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"localparam in a loop-generate block", false,
       "module m;\n  specparam sp = 2;\n"
       "  for (genvar i = 0; i < 2; i++) begin : g\n"
       "    localparam int p = sp * i;\n  end\nendmodule\n",
       "parameter references specparam 'sp'", 4, "6.20.5"},
      {"class port parameter of a class declared in the module", false,
       "module m;\n  specparam sp = 2;\n  class C #(int P = sp);\n"
       "  endclass\nendmodule\n",
       "parameter references specparam 'sp'", 3, "6.20.5"},
      {"class body parameter of a class declared in the module", false,
       "module m;\n  specparam sp = 2;\n  class C;\n"
       "    localparam int Q = sp;\n  endclass\nendmodule\n",
       "parameter references specparam 'sp'", 4, "6.20.5"},
      {"class body parameter of a class nested in one declared in the module",
       false,
       "module m;\n  specparam sp = 2;\n  class C;\n    class D;\n"
       "      localparam int Q = sp;\n    endclass\n  endclass\nendmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"localparam in a function", false,
       "module m;\n  specparam sp = 2;\n  function int f();\n"
       "    localparam int L = sp;\n    return L;\n  endfunction\n"
       "endmodule\n",
       "parameter references specparam 'sp'", 4, "6.20.5"},
      {"localparam in a task", false,
       "module m;\n  specparam sp = 2;\n  int x;\n  task t();\n"
       "    localparam int L = sp;\n    x = L;\n  endtask\nendmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"localparam in an initial block", false,
       "module m;\n  specparam sp = 2;\n  int x;\n  initial begin\n"
       "    localparam int L = sp;\n    x = L;\n  end\nendmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"localparam in a method of a class declared in the module", false,
       "module m;\n  specparam sp = 2;\n  class C;\n    function int f();\n"
       "      localparam int L = sp;\n      return L;\n    endfunction\n"
       "  endclass\nendmodule\n",
       "parameter references specparam 'sp'", 5, "6.20.5"},
      {"named instance override", true,
       "module m;\n  specparam sp = 2;\n  c #(.P(sp)) u();\nendmodule\n",
       "parameter override references specparam 'sp'", 6, "6.20.5"},
      {"positional instance override", true,
       "module m;\n  specparam sp = 2;\n  c #(sp + 1) u();\nendmodule\n",
       "parameter override references specparam 'sp'", 6, "6.20.5"},
      {"instance override in a generate block", true,
       "module m;\n  specparam sp = 2;\n  if (1) begin : g\n"
       "    c #(.P(sp)) u();\n  end\nendmodule\n",
       "parameter override references specparam 'sp'", 7, "6.20.5"},
      {"defparam value", true,
       "module m;\n  specparam sp = 2;\n  c u();\n  defparam u.P = sp;\n"
       "endmodule\n",
       "defparam right-hand side must be a constant expression built from "
       "numbers and parameters",
       7, "23.10.1"},
      {"defparam aimed at a module-body specparam", true,
       "module m;\n  c u();\n  defparam u.sp = 5;\nendmodule\n",
       "defparam cannot override specparam 'sp'", 6, "6.20.5"},
      {"defparam aimed at a specparam through an absolute path", true,
       "module m;\n  c u();\n  defparam m.u.sp = 5;\nendmodule\n",
       "defparam cannot override specparam 'sp'", 6, "6.20.5"},
      {"defparam aimed at a specify-block specparam", false,
       "module d(input a, output b);\n  specify\n    specparam sd = 1;\n"
       "  endspecify\nendmodule\nmodule m;\n  d u(.a(), .b());\n"
       "  defparam u.sd = 5;\nendmodule\n",
       "defparam cannot override specparam 'sd'", 8, "6.20.5"},
      {"named instance override aimed at a specparam", true,
       "module m;\n  c #(.sp(5)) u();\nendmodule\n",
       "module 'c' has no parameter 'sp'", 5, "23.10.2.2"},
  };
  for (const SpecparamUse& use : kUses) {
    SCOPED_TRACE(use.where);
    ElabFixture f;
    ElaborateSrc(std::string(use.instantiates_child ? kChild : "") + use.src,
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), use.message, use.line,
                              use.subclause));
  }
}

TEST(SpecparamElaboration, DefparamAimedAtASpecparamLeavesItsValue) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "module leaf;\n"
      "  specparam sp = 1;\n"
      "endmodule\n"
      "module m;\n"
      "  leaf u();\n"
      "  defparam u.sp = 5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override specparam 'sp'", 6,
                            "6.20.5"));
  ASSERT_NE(design, nullptr);
  const RtlirVariable* sp = FindVar(design, "leaf", "sp");
  ASSERT_NE(sp, nullptr);
  ASSERT_NE(sp->init_expr, nullptr);
  EXPECT_EQ(sp->init_expr->int_val, 1u);
}

TEST(SpecparamElaboration, ParameterValueNamingAParameterIsAcceptedEverywhere) {
  const char* const kSources[] = {
      "module ram16gen;\n  specparam dhold = 1.0;\n  specparam ddly = dhold;\n"
      "  parameter width = 1;\n  parameter regsize = width + 1;\nendmodule\n",
      "module m;\n  specparam sp = 2;\n  parameter int W = 2;\n"
      "  if (1) begin : g\n    parameter int p = W;\n"
      "  end else begin : h\n    localparam int p = W + 1;\n  end\n"
      "  case (1)\n    1: begin : k\n      localparam int p = W;\n    end\n"
      "  endcase\n  for (genvar i = 0; i < 2; i++) begin : r\n"
      "    localparam int p = W * i;\n  end\nendmodule\n",
      "module m;\n  specparam sp = 2;\n  parameter int W = 2;\n"
      "  class C #(int P = W);\n    localparam int Q = W;\n"
      "    class D;\n      localparam int R = W;\n    endclass\n"
      "    function int f();\n      localparam int L = W;\n      return L;\n"
      "    endfunction\n  endclass\nendmodule\n",
      "module m;\n  specparam sp = 2;\n  parameter int W = 2;\n  int x;\n"
      "  function int f();\n    localparam int L = W;\n    return L;\n"
      "  endfunction\n  task t();\n    localparam int L = W;\n    x = L;\n"
      "  endtask\n  initial begin\n    localparam int L = W;\n    x = L;\n"
      "  end\nendmodule\n",
      "module c #(parameter int P = 1);\n  specparam sp = 1;\nendmodule\n"
      "module m;\n  specparam sp = 2;\n  parameter int W = 2;\n"
      "  c #(.P(W)) u();\n  c #(W + 1) v();\n  c w();\n  defparam w.P = W;\n"
      "  if (1) begin : g\n    c #(.P(W)) x();\n  end\nendmodule\n",
      "module m;\n  specparam sp = 2;\n  if (1) begin : g\n"
      "    localparam int sp = 3;\n    localparam int p = sp;\n  end\n"
      "  class C #(int sp = 3);\n    localparam int Q = sp;\n  endclass\n"
      "  function int f();\n    localparam int sp = 3;\n"
      "    localparam int L = sp;\n    return L;\n  endfunction\n"
      "endmodule\n",
  };
  for (const char* src : kSources) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    for (const Diagnostic& diag : f.diag.Diagnostics()) {
      if (diag.severity == DiagSeverity::kError)
        ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
    }
  }
}

}  // namespace
