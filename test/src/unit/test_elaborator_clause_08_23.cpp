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

// §8.23: while a type parameter may resolve to a class type, use of the class
// scope resolution operator to select something through such a prefix is
// restricted to typedef declarations, the type operator, and type parameter
// assignments. A type parameter prefixing '::' in an expression is outside the
// permitted contexts and must be reported. This is the same restriction stated
// by §6.20.3 and enforced by the shared elaborator check.
TEST(ClassScopeResolutionElaboration, TypeParamScopePrefixRestricted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  static int val = 7;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type T = C;\n"
      "  int x;\n"
      "  initial x = T::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §8.23: the same restriction holds when the type parameter comes from the
// parameter port list and the '::' prefix appears inside a procedural always
// block (here on the right side of a nonblocking assignment), confirming the
// restriction is enforced across these contexts rather than only in an initial
// block with a body-declared type parameter.
TEST(ClassScopeResolutionElaboration,
     PortTypeParamScopePrefixInAlwaysBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  logic clk;\n"
      "  logic q;\n"
      "  always @(posedge clk) q <= T::n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §8.23: an ordinary class type name remains a valid scope resolution prefix in
// an expression; the restriction applies only to a type parameter prefix.
TEST(ClassScopeResolutionElaboration, ClassNamePrefixInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int val = 7;\n"
             "endclass\n"
             "module m;\n"
             "  parameter type T = int;\n"
             "  T data;\n"
             "  int x;\n"
             "  initial x = C::val;\n"
             "endmodule\n"));
}

}  // namespace
