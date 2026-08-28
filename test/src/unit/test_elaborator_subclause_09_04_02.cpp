

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event expression references non-singular variable "
                            "'arr'; event expressions shall return singular "
                            "values",
                            3, "9.4.2"));
}

TEST(EventControlElaboration, UnpackedStructEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "  initial @(s) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event expression references non-singular variable "
                            "'s'; event expressions shall return singular "
                            "values",
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

// §9.4.2: an aggregate object may appear in an event expression when the
// expression reduces to a singular value. Selecting a singular member of an
// otherwise non-singular unpacked struct is accepted (contrast @(s), which is
// rejected because the whole struct is non-singular).
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event expression calls function 'f' whose return "
                            "type is non-singular; event expressions shall "
                            "return singular values",
                            5, "9.4.2"));
}

// §9.4.2 says "Event expressions shall return singular values" and puts no
// condition on where the statement the event control precedes stands. A.6.4
// makes a procedural_timing_control_statement a statement_item, so an event
// control may be written in every position a statement holds a statement in,
// and the clause's own example writes three of them inside a fork-join.
// WalkStmtForEventSingular in
// src/elaborator/elaborator_validate_subroutine_args.cpp had written out eight
// of the thirteen child-statement links Stmt declares, and now takes the list
// from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The
// cases below cover one newly reached position each.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser keeps in Stmt::fork_stmts. §9.4.2's own example puts
// its event controls in exactly this position.
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

// A.6.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
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

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items.
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

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. The parser keeps them in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
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

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
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

}  // namespace
