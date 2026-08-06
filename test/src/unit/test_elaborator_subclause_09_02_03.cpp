#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FinalProcedureElaboration, DelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final #5 x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, EventControlInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  final @(posedge clk) x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, WaitInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final wait(x) x = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, ForkJoinInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  final begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, ValidFinalBlockNoErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, ElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(FinalProcedureElaboration, MultipleFinalProcedures) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final a = 1;\n"
      "  final b = 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  int count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST(FinalProcedureElaboration, FinalAndInitialCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool has_initial = false, has_final = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) has_initial = true;
    if (p.kind == RtlirProcessKind::kFinal) has_final = true;
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_final);
}

TEST(FinalProcedureElaboration, WaitForkInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  final begin\n"
      "    wait fork;\n"
      "    a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, NestedDelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final begin\n"
      "    x = 0;\n"
      "    #1 x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, DelayInNestedIfErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final begin\n"
      "    if (x)\n"
      "      #1 x = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, DelayInCaseBranchErrors) {
  // §9.2.3: only statements permitted inside a function declaration are allowed
  // in a final procedure, so a timing control nested inside a case branch is
  // rejected just as one nested inside an if is.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic x;\n"
      "  final begin\n"
      "    case (sel)\n"
      "      2'b00: #1 x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, CaseBranchWithoutTimingValid) {
  // Companion accept path: a case whose branches only assign is function-legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic x;\n"
      "  final begin\n"
      "    case (sel)\n"
      "      2'b00: x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, IntraAssignDelayInFinalErrors) {
  // §9.2.3: a final procedure admits only the timing-free statements permitted
  // in a function. A blocking assignment is a legal statement kind, but an
  // intra-assignment delay attaches a timing control to it and must be rejected
  // — a distinct syntactic form from a statement-leading delay.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = #5 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, IntraAssignEventControlInFinalErrors) {
  // Companion form: an intra-assignment event control is likewise a timing
  // control and is rejected inside a final procedure.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  final x = @(posedge clk) y;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, IntraAssignNonblockingDelayInFinalErrors) {
  // §9.2.3: the timing-control prohibition applies to a nonblocking assignment
  // carrying an intra-assignment delay too, not only the blocking form — a
  // distinct assignment kind. (Such a delay is legal in some always procedures,
  // but a final procedure admits no timing control at all.)
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x <= #5 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FinalProcedureElaboration, IfStatementInFinalValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, y;\n"
      "  final if (x) y = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, DisplayCallInFinalValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  final $display(\"statistics\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, FunctionCallInFinalValid) {
  // §9.2.3: a final procedure admits exactly the statements a function permits.
  // A call to a user-defined function (declared with real §13.4 syntax) is such
  // a statement, so it elaborates without error — the accept companion to the
  // timing-control and fork-join rejections above.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int doubler(int a); return a * 2; endfunction\n"
      "  int x;\n"
      "  final x = doubler(21);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
