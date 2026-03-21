#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CastOperatorParsing, CastingTypeString) {
  auto r = Parse(
      "module m;\n"
      "  initial begin string s; s = string'(65); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, CastingTypeConst) {
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = const'(42); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, CastingTypeUserDefined) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  initial begin byte_t x; x = byte_t'(16'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, TypeCastToStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  s_t s;\n"
      "  initial s = s_t'(16'hBEEF);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, NonblockingCastRhs) {
  auto r = Parse(
      "module m;\n"
      "  int q;\n"
      "  initial begin\n"
      "    q <= int'(3.14);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, BlockingCastRhs) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  real b;\n"
      "  initial begin\n"
      "    a = int'(b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, PackedCastToInt) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [15:0] a;\n"
      "    logic [15:0] b;\n"
      "  } wide_t;\n"
      "  wide_t w;\n"
      "  initial x = int'(w);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, IntCastToPackedStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(16'hBEEF);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, CastInParameterInit) {
  auto r = Parse(
      "module m;\n"
      "  parameter int P = int'(3.14);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
}

TEST(CastOperatorParsing, IntCastFromRealLiteral) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = int'(3.14);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}


TEST(CastOperatorParsing, CastCompatibleRealToInt) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastOperatorParsing, StringCastFromInteger) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    string s;\n"
              "    s = string'(8'h41);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, UserDefinedEnumCast) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  typedef enum {a, b, c, d} e;\n"
               "  initial begin\n"
               "    e val;\n"
               "    val = a;\n"
               "    val = e'(val + 1);\n"
               "  end\n"
               "endmodule\n"));
}

TEST(CastOperatorParsing, IntCastAstFields) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->text, "int");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(CastOperatorParsing, SignedCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = signed'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "signed");
}

TEST(CastOperatorParsing, ConstCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = const'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "const");
}

TEST(CastOperatorParsing, IntCastFromRealVar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 3.7;\n"
              "  int i;\n"
              "  initial i = int'(r);\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, ShortrealCast) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int i = 42;\n"
              "  shortreal sr;\n"
              "  initial sr = shortreal'(i);\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, SizeCastLiteral) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  logic [16:0] result;\n"
      "  initial result = 17'(x - 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, SizeCastParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter P = 17;\n"
              "  parameter Q = 16;\n"
              "  logic [31:0] x;\n"
              "  logic [31:0] r1, r2;\n"
              "  initial begin\n"
              "    r1 = P'(x - 2);\n"
              "    r2 = (Q+1)'(x - 2);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, CastRealExprToInt) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int result;\n"
              "  initial result = int'(2.0 * 3.0);\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, CastConcatShortint) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  shortint result;\n"
              "  initial result = shortint'({8'hFA, 8'hCE});\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, UnsignedCast) {
  auto r = Parse(
      "module m;\n"
      "  initial x = unsigned'(-4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
  EXPECT_EQ(stmt->rhs->text, "unsigned");
}

TEST(CastOperatorParsing, VoidCast) {
  auto r = Parse(
      "module m;\n"
      "  function void f(); endfunction\n"
      "  initial void'(f());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, LongintCast) {
  auto r = Parse(
      "module m;\n"
      "  longint x;\n"
      "  initial x = longint'(32'hDEADBEEF);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "longint");
}

TEST(CastOperatorParsing, CastInContinuousAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a;\n"
              "  logic [31:0] y;\n"
              "  assign y = int'(a);\n"
              "endmodule\n"));
}

TEST(CastOperatorParsing, NestedCast) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = signed'(shortint'(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "signed");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->lhs->text, "shortint");
}

TEST(CastOperatorParsing, CastInBinaryExpr) {
  auto r = Parse(
      "module m;\n"
      "  int a, b, c;\n"
      "  initial c = int'(a) + int'(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kCast);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kCast);
}

}  // namespace
