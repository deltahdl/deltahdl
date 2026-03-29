#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ClassConstructorParsing, BlockingAssignment_ClassNew) {
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

TEST(ClassConstructorParsing, BlockingAssignment_ClassNewWithArgs) {
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

TEST(ClassConstructorParsing, NewExpression) {
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

TEST(ClassConstructorParsing, NewWithArgs) {
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

TEST(ClassConstructorParsing, DeclarationNewWithArgs) {
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

TEST(ClassConstructorParsing, ImplicitConstructor) {
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

TEST(ClassConstructorParsing, ConstructorStaticError) {
  auto r = Parse(
      "class C;\n"
      "  static function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassConstructorParsing, ConstructorVirtualError) {
  auto r = Parse(
      "class C;\n"
      "  virtual function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassConstructorParsing, ConstructorNoReturnType) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  auto* method = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(method->name, "new");
}

TEST(ClassConstructorParsing, ConstructorWithDefaultArgs) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  bit [12:0] address;\n"
      "  int cmd_time;\n"
      "  function new(int cmd = 0, bit [12:0] adrs = 0, int t = 0);\n"
      "    command = cmd;\n"
      "    address = adrs;\n"
      "    cmd_time = t;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, ConstructorEndlabelNew) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, PropertyWithExplicitDefault) {
  auto r = Parse(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  int c3 = 1;\n"
      "  function new(int a);\n"
      "    c2 = 2;\n"
      "    c3 = a;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, DerivedClassWithPropertyDefaults) {
  auto r = Parse(
      "class C;\n"
      "  int c1 = 1;\n"
      "  function new(int a);\n"
      "    c1 = a;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  int d1 = 4;\n"
      "  function new;\n"
      "    super.new(d1);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, DeclarationClassNewNoArgs) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
