#include <gtest/gtest.h>

#include <initializer_list>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EventControlElaboration, PosedgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, NegedgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(negedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, AnyChangeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r, q;\n"
      "  always @(r) q = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, EdgeSensitivityPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst_n, d, q;\n"
      "  always_ff @(posedge clk or negedge rst_n)\n"
      "    if (!rst_n) q <= 0;\n"
      "    else q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) {
      ASSERT_EQ(p.sensitivity.size(), 2u);
      EXPECT_EQ(p.sensitivity[0].edge, Edge::kPosedge);
      EXPECT_EQ(p.sensitivity[1].edge, Edge::kNegedge);
    }
  }
}

TEST(EventControlElaboration, EdgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(edge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (!p.sensitivity.empty()) {
      EXPECT_EQ(p.sensitivity[0].edge, Edge::kEdge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(EventControlElaboration, TaskCallInEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial @(t()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' cannot be called in an event expression",
                            3, "9.4.2"));
}

TEST(EventControlElaboration, TaskCallInIffGuardRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  task t; endtask\n"
      "  initial @(posedge clk iff t()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' cannot be called in an event expression",
                            4, "9.4.2"));
}

TEST(EventControlElaboration, UnpackedArrayEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial @(arr) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "event expression references non-singular variable "
                    "'arr'; an event can only be watched on a singular value",
                    3, "9.4.2"));
}

TEST(EventControlElaboration, IntraAssignmentEventMustBeSingular) {
  ElabFixture f;
  ElaborateSrc(
      "module m; int arr[4]; int x, y;\n"
      "  initial x = @(arr) 1;\n"
      "  initial x <= @(arr) 2;\n"
      "  initial y = @(arr[0]) 3;\n"
      "endmodule\n",
      f);
  for (const int kLine : {2, 3}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "event expression references non-singular variable 'arr'",
                      kLine, "9.4.2"))
        << kLine;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "non-singular", 4, "9.4.2"));
}

TEST(EventControlElaboration, UnpackedStructEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "  initial @(s) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "event expression references non-singular variable "
                    "'s'; an event can only be watched on a singular value",
                    3, "9.4.2"));
}

TEST(EventControlElaboration, PackedStructEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  struct packed { logic a; logic b; } s;\n"
      "  initial @(s) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, UnpackedStructMemberEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "  initial @(s.a) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, FunctionCallInEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function bit f; return 1; endfunction\n"
      "  initial @(f()) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration,
     FunctionReturningUnpackedStructInEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function struct { int a; int b; } f;\n"
      "    f.a = 0;\n"
      "  endfunction\n"
      "  initial @(f()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression calls function 'f' whose return "
      "type is non-singular; an event can only be watched on a singular value",
      5, "9.4.2"));
}

TEST(EventControlElaboration, NonSingularEventExpressionInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial fork\n"
      "    @(arr) ;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 4, "9.4.2"));
}

TEST(EventControlElaboration,
     NonSingularEventExpressionInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial assert (1) @(arr) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 3, "9.4.2"));
}

TEST(EventControlElaboration,
     NonSingularEventExpressionInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial assert (1) else @(arr) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 3, "9.4.2"));
}

TEST(EventControlElaboration,
     NonSingularEventExpressionInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial randcase\n"
      "    1 : @(arr) ;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 4, "9.4.2"));
}

TEST(EventControlElaboration,
     NonSingularEventExpressionInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { @(arr) ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 5, "9.4.2"));
}

TEST(EventControlElaboration,
     NonSingularEventExpressionInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  int i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { @(arr) ; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "event expression references non-singular variable 'arr'", 6, "9.4.2"));
}

TEST(EventControlElaboration,
     DISABLED_AClassTaskCalledInAnEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class P;\n"
      "  task t(); endtask\n"
      "endclass\n"
      "module m;\n"
      "  P p = new;\n"
      "  initial @(p.t()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' cannot be called in an event expression",
                            6, "9.4.2"));
}

}  // namespace
