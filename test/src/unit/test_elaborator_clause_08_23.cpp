#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionElaboration, ScopeResolutionTypedefOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module m;\n"
             "  Cfg::my_type x;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ScopeResolutionStaticMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Utils;\n"
             "  static function void compute();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial Utils::compute();\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ScopeResolutionParameterOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m;\n"
             "  logic [Cfg::WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, NestedClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    int val;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, SuperclassScopeAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
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

TEST(ClassScopeResolutionElaboration, StaticPropertyReadOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int count;\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = C::count;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, EnumAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  typedef enum {bin, oct, dec, hex} radix;\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = Base::bin;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ChainedScopeOk) {
  EXPECT_TRUE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    static int x;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = Outer::Inner::x;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, LocalparamAccessOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  localparam int SIZE = 16;\n"
             "endclass\n"
             "module m;\n"
             "  logic [C::SIZE-1:0] data;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, DisambiguationOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  typedef enum {bin, oct, dec, hex} radix;\n"
             "  static task print(radix r, integer n);\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  int bin = 123;\n"
             "  initial Base::print(Base::bin, bin);\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, NestedClassAsTypeOk) {
  EXPECT_TRUE(
      ElabOk("class StringList;\n"
             "  class Node;\n"
             "    string name;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "  StringList::Node n;\n"
             "endmodule\n"));
}

}  // namespace
