#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralBlockSyntaxParsing, BlockingAssignment_ClassNew) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ProceduralBlockSyntaxParsing, BlockingAssignment_ClassNewWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(1, 2); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ClassParsing, NewExpression) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassParsing, NewWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "    function new(int val);\n"
      "      a = val;\n"
      "    endfunction\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = new(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(DeclarationAssignmentParsing, ClassNewWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int a, int b);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NumberParsing, ImplicitConstructor) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
