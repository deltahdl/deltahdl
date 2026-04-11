#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AlwaysCombParsing, NestedIfElseAndCase) {
  auto r = Parse(
      "module m;\n"
      "  logic mode;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] out;\n"
      "  always_comb begin\n"
      "    if (mode) begin\n"
      "      case (sel)\n"
      "        2'd0: out = 8'd10;\n"
      "        2'd1: out = 8'd20;\n"
      "        default: out = 8'd0;\n"
      "      endcase\n"
      "    end else begin\n"
      "      out = 8'd0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);

  ASSERT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->then_branch->stmts.size(), 1u);
  EXPECT_EQ(stmt->then_branch->stmts[0]->kind, StmtKind::kCase);
}

TEST(AlwaysCombParsing, ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data_in [0:3];\n"
      "  logic [7:0] data_out [0:3];\n"
      "  always_comb begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      data_out[i] = data_in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(AlwaysCombParsing, BlockInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(AlwaysCombParsing, AlwaysCombMultipleAssigns) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = a ^ d;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysMultiAssigns(r);
}

TEST(AlwaysCombParsing, MultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, x, y, z;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = b ^ c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

TEST(AlwaysCombParsing, AlwaysCombNestedIfElseInBlock) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      if (b) y = 1;\n"
      "      else y = 2;\n"
      "    else\n"
      "      y = 0;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysNestedIfElse(r);
}

TEST(AlwaysCombParsing, AlwaysCombWithCaseInside) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kCase);
}

TEST(AlwaysCombParsing, MultipleAlwaysCombBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a & b;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysComb(r, 0);
  auto* second = NthAlwaysComb(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(second->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
}

TEST(AlwaysCombParsing, ArrayIndexing) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  logic [3:0] addr;\n"
      "  logic [7:0] data;\n"
      "  always_comb data = mem[addr];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
}

TEST(AlwaysCombParsing, AlwaysCombMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, sum, carry;\n"
      "  always_comb begin\n"
      "    sum = a ^ b;\n"
      "    carry = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

TEST(AlwaysCombParsing, ComplexMuxPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [3:0] sel;\n"
              "  logic [7:0] inputs [0:15];\n"
              "  logic [7:0] out;\n"
              "  always_comb begin\n"
              "    out = 8'd0;\n"
              "    for (int i = 0; i < 16; i++) begin\n"
              "      if (sel == i[3:0])\n"
              "        out = inputs[i];\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AlwaysCombParsing, AlwaysCombAlwaysKind) {
  auto r = Parse(
      "module m;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

TEST(AlwaysCombParsing, AlwaysCombBodyDirectAssign) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(AlwaysCombParsing, AlwaysCombBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(AlwaysCombParsing, PriorityEncoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] enc;\n"
      "  logic valid;\n"
      "  always_comb begin\n"
      "    enc = 2'b00;\n"
      "    valid = 1'b0;\n"
      "    if (req[3]) begin\n"
      "      enc = 2'b11;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[2]) begin\n"
      "      enc = 2'b10;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[1]) begin\n"
      "      enc = 2'b01;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[0]) begin\n"
      "      enc = 2'b00;\n"
      "      valid = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);

  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kIf);
}

TEST(AlwaysCombParsing, AlwaysCombIfElse) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

TEST(AlwaysCombParsing, AlwaysCombCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

TEST(AlwaysCombParsing, AlwaysCombComplexLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b, c, y;\n"
      "  always_comb y = (a > b) ? (a + c) : (b - c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

TEST(AlwaysCombParsing, SimpleBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(AlwaysCombParsing, BeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(AlwaysCombParsing, AlwaysCombBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, y;\n"
      "  always_comb begin\n"
      "    a = b & c;\n"
      "    y = a | b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

TEST(AlwaysCombParsing, AlwaysCombWithIf) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
}

TEST(AlwaysCombParsing, CaseStatementWithDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
}

static ModuleItem* NthItem(ParseResult& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

TEST(AlwaysCombParsing, AssignInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic a; logic b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic sel;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      p = '{1'b1, 1'b0};\n"
      "    else\n"
      "      p = '{1'b0, 1'b1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 3);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
}

}  // namespace
