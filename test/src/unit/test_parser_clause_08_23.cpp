#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA221, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SourceText, ClassNestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(members[0]->nested_class->name, "Inner");
}

TEST(ParserSection8, ClassWithTypedef) {
  auto r = Parse(
      "class test_cls;\n"
      "  typedef enum {A = 10, B = 20} e_type;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "test_cls");
}

TEST(ParserSection8, NestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int x;\n"
      "  endclass\n"
      "  Inner inst;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Outer");
}

TEST(ParserSection8, ClassScopeResolutionStaticMethod) {
  auto r = Parse(
      "class Base;\n"
      "  static function void display();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial Base::display();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionEnum) {
  auto r = Parse(
      "class Base;\n"
      "  typedef enum {bin, oct, dec, hex} radix;\n"
      "endclass\n"
      "module m;\n"
      "  initial x = Base::bin;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionTypedef) {
  auto r = Parse(
      "class Outer;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  Outer::my_type x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionParameter) {
  auto r = Parse(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  logic [Cfg::WIDTH-1:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserClause03, Cl3_13_ClassScopeResolution) {
  EXPECT_TRUE(
      ParseOk("class base;\n"
              "  typedef int my_type;\n"
              "endclass\n"
              "module m;\n"
              "  base::my_type x;\n"
              "endmodule\n"));
}

TEST(ParserSection8_23, ChainedClassScope) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    static int x;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  initial y = Outer::Inner::x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection8_23, SuperclassScopeAccess) {
  auto r = Parse(
      "class Base;\n"
      "  static int count;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int get_count();\n"
      "    return Base::count;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
