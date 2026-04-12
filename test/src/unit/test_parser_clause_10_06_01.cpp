#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralAssignDeassignParsing, AssignWithBitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q[0] = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ProceduralAssignDeassignParsing, AssignInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg q;\n"
              "  task set_q;\n"
              "    assign q = 1;\n"
              "  endtask\n"
              "  task clear_q;\n"
              "    deassign q;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(ProceduralAssignDeassignParsing, InterleavedWithNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    q <= 0;\n"
      "    deassign q;\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto [s0, s1, s2, s3] = Get4InitialStmts(r);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s3->kind, StmtKind::kNonblockingAssign);
}

TEST(ProceduralAssignDeassignParsing, FullDFlipFlopPattern) {
  auto r = Parse(
      "module dff_full(output reg q, input d, clr, pre, clk);\n"
      "  always @(clr or pre) begin\n"
      "    if (!clr)\n"
      "      assign q = 0;\n"
      "    else if (!pre)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      deassign q;\n"
      "  end\n"
      "  always @(posedge clk)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "dff_full");

  int always_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) always_count++;
  }
  EXPECT_GE(always_count, 2);
}

TEST(ProceduralAssignDeassignParsing, AssignInAlwaysBlock) {
  auto r = Parse(
      "module dff(output q, input d, clear, preset, clock);\n"
      "  logic q;\n"
      "  always @(clear or preset)\n"
      "    if (!clear) assign q = 0;\n"
      "    else if (!preset) assign q = 1;\n"
      "    else deassign q;\n"
      "  always @(posedge clock) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "dff");
}
TEST(ProceduralAssignDeassignParsing, AssignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ProceduralAssignDeassignParsing, AssignInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, DeassignInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, AssignExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    assign c = a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(ProceduralAssignDeassignParsing, AssignConcatenationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] out;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    assign out = {a, b, c, d};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

TEST(ProceduralAssignDeassignParsing, AssignBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, AssignPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3:0] = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, AssignConcatLhsThreeRegs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    assign {a, b, c} = 3'b101;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

TEST(ProceduralAssignDeassignParsing, DeassignConcatLhsThreeRegs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    deassign {a, b, c};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

TEST(ProceduralAssignDeassignParsing, AssignInIfElse) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      assign q = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kAssign);
}

TEST(ProceduralAssignDeassignParsing, AssignInCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: assign q = 0;\n"
      "      2'b01: assign q = 1;\n"
      "      default: deassign q;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kDeassign);
}


TEST(ProceduralAssignDeassignParsing, AssignInAlwaysWithEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg q, clear;\n"
      "  always @(clear)\n"
      "    if (!clear) assign q = 0;\n"
      "    else deassign q;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];

  ModuleItem* always_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      always_item = item;
      break;
    }
  }
  ASSERT_NE(always_item, nullptr);
  ASSERT_NE(always_item->body, nullptr);
}

TEST(ProceduralAssignDeassignParsing, MultipleAssignsDifferentVars) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    assign a = 1;\n"
      "    assign b = 0;\n"
      "    assign c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s2->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
}

TEST(ProceduralAssignDeassignParsing, DeassignThenProceduralAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
}

TEST(ProceduralAssignDeassignParsing, AssignTernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    assign q = sel ? a : b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(ProceduralAssignDeassignParsing, AssignFunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    assign q = compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ProceduralAssignDeassignParsing, AssignUnaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, q;\n"
      "  initial begin\n"
      "    assign q = ~a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

TEST(ProceduralAssignDeassignParsing, AssignInsideForLoop) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] q;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      assign q[i] = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kAssign);
}

TEST(ProceduralAssignDeassignParsing, DFlipFlopClearPreset) {
  EXPECT_TRUE(
      ParseOk("module dff_cp(output reg q, input d, clear, preset, clock);\n"
              "  always @(clear or preset)\n"
              "    if (!clear)\n"
              "      assign q = 0;\n"
              "    else if (!preset)\n"
              "      assign q = 1;\n"
              "    else\n"
              "      deassign q;\n"
              "  always @(posedge clock)\n"
              "    q <= d;\n"
              "endmodule\n"));
}

TEST(ProceduralAssignDeassignParsing, AssignInNamedBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin : my_block\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

TEST(ProceduralAssignDeassignParsing, AssignInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      assign a = 1;\n"
      "      assign b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kAssign);
}

}

TEST(ProceduralAssignDeassignParsing, DeassignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ProceduralAssignDeassignParsing, AssignSystemFuncRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] q;\n"
      "  initial begin\n"
      "    assign q = $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(ProceduralAssignDeassignParsing, MultipleAssignsSameVar) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, "q");
  EXPECT_EQ(s1->lhs->text, "q");
}

TEST(ProceduralAssignDeassignParsing, DeassignMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    deassign a;\n"
      "    deassign b;\n"
      "    deassign c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kDeassign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
}

TEST(ProceduralAssignDeassignParsing, DelayBeforeAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    #10 assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProceduralAssignDeassignParsing, AssignNestedIfElse) {
  auto r = Parse(
      "module m;\n"
      "  reg q, a, b;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b)\n"
      "        assign q = 1;\n"
      "      else\n"
      "        assign q = 0;\n"
      "    else\n"
      "      deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);

  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kAssign);

  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kDeassign);
}

TEST(ProceduralAssignDeassignParsing, AssignReductionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  reg parity;\n"
      "  initial begin\n"
      "    assign parity = ^data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

TEST(ProceduralAssignDeassignParsing, AssignToVector) {
  auto r = Parse(
      "module m;\n"
      "  reg [15:0] vec;\n"
      "  initial begin\n"
      "    assign vec = 16'hDEAD;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "vec");
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, DeassignSingularVariable) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

TEST(ProceduralAssignDeassignParsing, AssignSingularVariableLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

TEST(ProceduralAssignDeassignParsing, ReAssignSameVariableSyntax) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, s1->lhs->text);
}

}  // namespace
