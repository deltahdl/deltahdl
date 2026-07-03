#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(UpwardNameReferenceParsing, UpwardReferenceToNet) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  assign w = parent.n;\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceToParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  localparam int K = parent.P;\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceToPort) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = parent.p;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceToFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = parent.f(1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceToTaskCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    parent.t();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceToNamedBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = parent.blk.v;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceOnLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    parent.v = 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceInContinuousAssignLhs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic d;\n"
              "  assign parent.n = d;\n"
              "endmodule\n"));
}

TEST(UpwardNameReferenceParsing, UpwardReferenceProducesMemberAccessNode) {
  auto r = Parse(
      "module m;\n"
      "  initial x = parent.v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->lhs->text, "parent");
  ASSERT_NE(stmt->rhs->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->rhs->text, "v");
}

TEST(UpwardNameReferenceParsing, MultiComponentUpwardPathParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = parent.inst.sub.v;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
