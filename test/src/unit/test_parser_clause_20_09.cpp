#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskExtendedParsing, CountonesParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countones(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(OptionalSystemTaskExtendedParsing, IsunknownParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $isunknown(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(OptionalSystemTaskExtendedParsing, Onehot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = $onehot(state);\n"
      "    y = $onehot0(state);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// list_of_control_bits ::= control_bit { , control_bit }
// The grammar permits one or more control_bit entries after the expression
// argument. Cover the multi-entry case explicitly.
TEST(OptionalSystemTaskExtendedParsing, CountbitsMultipleControlBits) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countbits(data, 1'b1, 1'b0, 1'bx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  // expression argument plus three control_bit entries.
  EXPECT_EQ(stmt->rhs->args.size(), 4u);
}

// §20.9 explicitly states the control_bit arguments may be variables; the
// parser must therefore accept identifier-shaped expressions for them.
TEST(OptionalSystemTaskExtendedParsing, CountbitsVariableControlBit) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countbits(data, ctrl0, ctrl1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  ASSERT_EQ(stmt->rhs->args.size(), 3u);
  EXPECT_EQ(stmt->rhs->args[1]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->args[2]->kind, ExprKind::kIdentifier);
}

}  // namespace
