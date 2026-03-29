#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ClassScopeResolutionParsing, TypedefAccess) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, StaticMethodCall) {
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

TEST(ClassScopeResolutionParsing, EnumMemberAccess) {
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

TEST(ClassScopeResolutionParsing, TypedefAsType) {
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

TEST(ClassScopeResolutionParsing, ParameterAccess) {
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

TEST(ClassScopeResolutionParsing, TypedefInModuleScope) {
  EXPECT_TRUE(
      ParseOk("class base;\n"
              "  typedef int my_type;\n"
              "endclass\n"
              "module m;\n"
              "  base::my_type x;\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, ChainedClassScope) {
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

TEST(ClassScopeResolutionParsing, SuperclassScopeAccess) {
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

TEST(ClassScopeResolutionParsing, StaticPropertyRead) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = C::count;\n"
      "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, StaticPropertyWrite) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module m;\n"
      "  initial C::count = 5;\n"
      "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, ScopeAsTypePrefix) {
  auto r = Parse(
      "class StringList;\n"
      "  class Node;\n"
      "    string name;\n"
      "  endclass\n"
      "endclass\n"
      "class StringTree;\n"
      "  class Node;\n"
      "    string name;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  StringList::Node n1;\n"
      "  StringTree::Node n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, StaticTaskCall) {
  EXPECT_TRUE(ParseOk(
      "class Logger;\n"
      "  static task log(string msg);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  initial Logger::log(\"hello\");\n"
      "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, DisambiguatesLocalFromClassMember) {
  EXPECT_TRUE(ParseOk(
      "class Base;\n"
      "  typedef enum {bin, oct, dec, hex} radix;\n"
      "  static task print(radix r, integer n);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  int bin = 123;\n"
      "  initial Base::print(Base::bin, bin);\n"
      "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, LocalparamAccess) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  localparam int SIZE = 16;\n"
      "endclass\n"
      "module m;\n"
      "  logic [C::SIZE-1:0] data;\n"
      "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, NestedClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(r.cu->classes[0]->members[0]->nested_class->name, "Inner");
}

}  // namespace
