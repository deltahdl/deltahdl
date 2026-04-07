#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LoopSyntaxParsing, ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever #5 clk = ~clk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while (count > 0) count = count - 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) a[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopNoInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (; i < 10; i++) a[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(LoopSyntaxParsing, ForLoopNoCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; ; i++) begin\n"
      "      if (i > 10) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, DoWhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do begin\n"
      "      count = count - 1;\n"
      "    end while (count > 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopPostIncrementStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopPostDecrementStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 255; i >= 0; i--) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++) begin\n"
      "      $display(\"%d\", i);\n"
      "      x = x + i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ForBodyBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      mem[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlockingAssign);
}

TEST(LoopSyntaxParsing, PostfixIncrementInForStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForWithIncrementStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForWithByteDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (byte b = 0; b < 100; b = b + 1)\n"
      "      data = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kByte);
}

TEST(LoopSyntaxParsing, ForWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i = i + 1) begin\n"
      "      a[i] = i;\n"
      "      b[i] = i * 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, IfElseInsideForBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 16; i = i + 1) begin\n"
      "      if (i[0]) odd[i] = 1;\n"
      "      else even[i] = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->for_body->stmts.size(), 1u);
  EXPECT_EQ(stmt->for_body->stmts[0]->kind, StmtKind::kIf);
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

TEST(LoopSyntaxParsing, ForLoopInAlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q [0:3];\n"
      "  logic [7:0] d [0:3];\n"
      "  always_latch begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      if (en) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFor);
  EXPECT_NE(item->body->stmts[0]->for_cond, nullptr);
  EXPECT_NE(item->body->stmts[0]->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForWithDecrement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 9; i >= 0; i--)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
  EXPECT_NE(stmt->for_step, nullptr);
}


TEST(LoopSyntaxParsing, ForIntDeclHasInitAndCond) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
}

TEST(LoopSyntaxParsing, ForIntDeclHasStepBodyType) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForWithLogicDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (logic [7:0] i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

TEST(LoopSyntaxParsing, ForIntDeclWithBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      $display(i);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForWithoutDeclStillWorks) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kImplicit);
}

TEST(LoopSyntaxParsing, ForIntDeclKindCheck) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(LoopSyntaxParsing, ForAllPartsNonNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopTypedInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForLoopUntypedInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kImplicit);
}

TEST(LoopSyntaxParsing, ForEmptyInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
}

TEST(LoopSyntaxParsing, ForEmptyCond) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; ; i++) begin\n"
      "      if (i == 10) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

TEST(LoopSyntaxParsing, ForEmptyStep) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10;) begin\n"
      "      i = i + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForAllEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (;;) break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
  EXPECT_EQ(stmt->for_cond, nullptr);
  EXPECT_EQ(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(LoopSyntaxParsing, ForVarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (var int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForLogicTypeInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (logic [7:0] i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

TEST(LoopSyntaxParsing, ForStepCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i += 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForStepPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForStepPreIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; ++i) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForStepPostDecrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; i--) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}
TEST(LoopSyntaxParsing, ForWithArrayBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++)\n"
      "      data[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

static ModuleItem* FirstFuncOrTask(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

static Stmt* FindStmtByKind(ModuleItem* item, StmtKind kind) {
  for (auto* stmt : item->func_body_stmts) {
    if (stmt->kind == kind) return stmt;
  }
  return nullptr;
}

TEST(LoopSyntaxParsing, ForLoopInitInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int sum_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForLoopInitInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_auto(int n);\n"
      "    int total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, AutomaticFuncWithForLoop) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_to_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  auto* for_stmt = FindStmtByKind(item, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_NE(for_stmt->for_cond, nullptr);
  EXPECT_NE(for_stmt->for_body, nullptr);
}

TEST(LoopSyntaxParsing, WhileLoopInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] val;\n"
      "  logic [3:0] count;\n"
      "  always_comb begin\n"
      "    count = 0;\n"
      "    while (val[count] && count < 8)\n"
      "      count = count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kWhile);
}

TEST(LoopSyntaxParsing, NestedForInsideWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (running) begin\n"
      "      for (int i = 0; i < 8; i = i + 1)\n"
      "        data[i] = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->body->stmts.size(), 1u);
  EXPECT_EQ(stmt->body->stmts[0]->kind, StmtKind::kFor);
}

TEST(LoopSyntaxParsing, WhileWithNullBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    while (0) ;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LoopSyntaxParsing, WhileSingleStatementBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, WhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

TEST(LoopSyntaxParsing, WhileLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (x > 0) begin\n"
      "      x = x - 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, DoWhileSingleStatementBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(LoopSyntaxParsing, DoWhileComplexCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do begin\n"
      "      x = x + 1;\n"
      "    end while (x < 10 && !done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, DoWhileDecrementBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do x = x - 1; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, DoWhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do ; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(LoopSyntaxParsing, DoWhileBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do begin x = x + 1; end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, DoWhileLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do begin\n"
      "      x = x + 1;\n"
      "    end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ForeverWithTimingControl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    forever begin\n"
              "      @(posedge clk);\n"
              "      x = ~x;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LoopSyntaxParsing, ForeverNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(LoopSyntaxParsing, ForeverLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      @(posedge clk);\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// --- Missing syntax coverage ---

TEST(LoopSyntaxParsing, ForStepPreDecrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; --i) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForStepFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = next_val(i)) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(LoopSyntaxParsing, ForVarLogicTypeDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (var logic [7:0] i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

// --- Error conditions ---

TEST(LoopSyntaxParsing, ErrorForMissingSemicolonAfterInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0 i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, ErrorForMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++ x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, ErrorWhileMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while x > 0) x = x - 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10)\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingWhileKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; (x < 10);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
