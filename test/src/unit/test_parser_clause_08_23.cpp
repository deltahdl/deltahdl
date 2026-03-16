#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(NetAndVariableTypeParsing, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassParsing, ClassScopeResolutionStaticMethod) {
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

TEST(ClassParsing, ClassScopeResolutionEnum) {
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

TEST(ClassParsing, ClassScopeResolutionTypedef) {
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

TEST(ClassParsing, ClassScopeResolutionParameter) {
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

TEST(DesignBuildingBlockParsing, ClassScopeResolution) {
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

}  // namespace
