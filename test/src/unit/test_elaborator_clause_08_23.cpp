#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.23: Class scope resolution of typedef in module — OK.
TEST(ElabA823, ScopeResolutionTypedefOk) {
  EXPECT_TRUE(ElabOk(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n"));
}

// §8.23: Class scope resolution of static method call — OK.
TEST(ElabA823, ScopeResolutionStaticMethodOk) {
  EXPECT_TRUE(ElabOk(
      "class Utils;\n"
      "  static function void compute();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial Utils::compute();\n"
      "endmodule\n"));
}

// §8.23: Class scope resolution of parameter — OK.
TEST(ElabA823, ScopeResolutionParameterOk) {
  EXPECT_TRUE(ElabOk(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  logic [Cfg::WIDTH-1:0] data;\n"
      "endmodule\n"));
}

// §8.23: Nested class declaration in class — OK.
TEST(ElabA823, NestedClassDeclOk) {
  EXPECT_TRUE(ElabOk(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.23: Superclass scope access from derived — OK.
TEST(ElabA823, SuperclassScopeAccessOk) {
  EXPECT_TRUE(ElabOk(
      "class Base;\n"
      "  static int count;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int get_count();\n"
      "    return Base::count;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n"));
}

}  // namespace
