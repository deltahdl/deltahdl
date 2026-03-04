// §6.24.1: Cast operator

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.2.2.1 Net and variable types
// =============================================================================
// --- casting_type ---
// simple_type | constant_primary | signing | string | const
TEST(ParserA221, CastingTypeSimpleInt) {
  // simple_type: integer_type cast
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = int'(3.14); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeSigning) {
  // signing: signed'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = signed'(8'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeString) {
  // string: string'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin string s; s = string'(65); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeConst) {
  // const: const'(expr)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = const'(42); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeUserDefined) {
  // casting_type with user-defined type (simple_type: ps_type_identifier)
  // Note: constant_primary'(expr) cast (e.g., N'(val)) requires semantic
  // analysis to distinguish from sized literals — tested via type casts.
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  initial begin byte_t x; x = byte_t'(16'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 17. Struct type cast from integer using type'(expr).
TEST(ParserSection7, Sec7_2_2_TypeCastToStruct) {
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
// --- 20. Nonblocking with cast RHS ---
TEST(ParserSection10, Sec10_4_2_CastRhs) {
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
// --- 25. Blocking assignment with cast: a = int'(b) ---
TEST(ParserSection10, Sec10_4_1_CastRhs) {
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
// --- Cast packed struct to integer type ---
TEST(ParserSection7, Sec7_2_1_PackedCastToInt) {
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

// --- Cast integer to packed struct type ---
TEST(ParserSection7, Sec7_2_1_IntCastToPackedStruct) {
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

// § constant_primary — constant_cast
TEST(ParserA84, ConstantPrimaryCast) {
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

// § primary — cast
TEST(ParserA84, PrimaryCast) {
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

// =============================================================================
// A.8.4 Primaries — cast and constant_cast
// =============================================================================
// § cast — type cast in expression
TEST(ParserA84, CastInExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § cast — signed cast
TEST(ParserA84, CastSigned) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = signed'(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § constant_cast — in parameter
TEST(ParserA84, ConstantCastInParam) {
  auto r = Parse("module m; parameter int P = int'(3.0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
}
// --- Cast expression ---
TEST(ParserSection11, Sec11_1_CastExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(3.14);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// Static cast with type apostrophe syntax: type'(expr).
TEST(ParserSection8, StaticCastTypeSyntax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    int a;\n"
              "    real r;\n"
              "    r = 3.14;\n"
              "    a = int'(r);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, CastCompatibleRealToInt) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

// =========================================================================
// §6.24.1: Static casting — type and size casts
// =========================================================================
TEST(ParserSection6, StaticCastRealToInt) {
  // §6.24.1: int'(2.0 * 3.0) casts real to int.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    int result;\n"
              "    result = int'(2.0 * 3.0);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, StaticCastStringType) {
  // §6.24.1: string'(expr) cast is valid per grammar.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    string s;\n"
              "    s = string'(8'h41);\n"
              "  end\n"
              "endmodule\n"));
}

// Step 2a: user-defined type cast (fixes 6.19.4-cast)
TEST(ParserSection6, TypeCast_UserDefined) {
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
// =========================================================================
// §6.6.8: Void data type (additional tests)
// =========================================================================
TEST(ParserSection6, VoidCastExpression) {
  auto r = Parse(
      "module t;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}
// =========================================================================
// §6.24: Casting
// =========================================================================
TEST(ParserSection6, IntCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

TEST(ParserSection6, IntCast_Details) {
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

TEST(ParserSection6, SignedCast) {
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

TEST(ParserSection6, ConstCast) {
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

TEST(ParserSection6, RealCastExplicit) {
  // Explicit cast: int'(real_val) (LRM 6.24)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 3.7;\n"
              "  int i;\n"
              "  initial i = int'(r);\n"
              "endmodule\n"));
}

TEST(ParserSection6, ShortrealCast) {
  // Cast to shortreal
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int i = 42;\n"
              "  shortreal sr;\n"
              "  initial sr = shortreal'(i);\n"
              "endmodule\n"));
}

}  // namespace
