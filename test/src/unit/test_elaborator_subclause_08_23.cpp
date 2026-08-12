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
// permitted contexts and must be reported. §6.20.3 states the type parameter
// case in its own words, so this leg is reported under that subclause and must
// stay there: extending the check to the other two prefix kinds §8.23 names,
// the incomplete forward type and the interface-based typedef, must not move
// the type parameter report to §8.23.
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
  const Diagnostic* diag = FindDiag(
      f, "type parameter 'T' may prefix the class scope resolution operator");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.20.3");
}

// §8.23: the same restriction holds when the type parameter comes from the
// parameter port list and the '::' prefix appears inside a procedural always
// block (here on the right side of a nonblocking assignment), confirming the
// restriction is enforced across these contexts rather than only in an initial
// block with a body-declared type parameter. §6.20.3 states the type parameter
// case in its own words, so this leg is reported under that subclause and must
// stay there when the check grows the two prefix kinds §8.23 adds.
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
  const Diagnostic* diag = FindDiag(
      f, "type parameter 'T' may prefix the class scope resolution operator");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.20.3");
}

// §8.23: an incomplete forward type is one of the three prefix kinds whose use
// with the class scope resolution operator is confined to a typedef
// declaration, the type operator, and a type parameter assignment. A forward
// type no definition in the scope completes is incomplete, so prefixing '::'
// with it in an expression is outside all three and is reported under §8.23.
TEST(ClassScopeResolutionElaboration, IncompleteForwardTypePrefixIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial x = C::val;\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f,
               "incomplete forward type 'C' may prefix the class scope "
               "resolution operator");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "8.23");
}

// §8.23: a type defined by an interface-based typedef, the §6.18 form that
// names a type through an interface port, is the third restricted prefix kind.
// Selecting through it in an expression is none of the three permitted
// contexts and is reported under §8.23.
TEST(ClassScopeResolutionElaboration, InterfaceBasedTypedefPrefixIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.data_t my_data_t;\n"
      "  int x;\n"
      "  initial x = my_data_t::val;\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f, "type 'my_data_t' defined by an interface-based typedef");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "8.23");
}

// §8.23 restricts an *incomplete* forward type, and §6.18 lets the definition
// that completes one appear before or after the forward declaration. A forward
// type a class in the scope resolves is therefore an ordinary class type name,
// and prefixing '::' with it in an expression stays legal. This guards the
// §8.23 check against rejecting the forward-declaration pattern §6.18 makes
// legal in either order.
TEST(ClassScopeResolutionElaboration, ResolvedForwardTypePrefixOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int val = 7;\n"
             "endclass\n"
             "module m;\n"
             "  typedef class C;\n"
             "  int x;\n"
             "  initial x = C::val;\n"
             "endmodule\n"));
}

// §8.23: a typedef declaration is the first of the three contexts in which a
// restricted prefix may precede the class scope resolution operator, so
// selecting a type out of a forward-declared class inside a typedef
// elaborates.
TEST(ClassScopeResolutionElaboration, ForwardTypePrefixInTypedefDeclOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef class Frame;\n"
             "  class Frame;\n"
             "    typedef byte payload_t;\n"
             "  endclass\n"
             "  typedef Frame::payload_t alias_t;\n"
             "endmodule\n"));
}

// §8.23: a type parameter assignment is the third context in which a restricted
// prefix may precede the class scope resolution operator. §6.20.3 writes that
// context as `localparam type C_t = C::T;` in the example it states the rule
// with, so selecting a type out of a forward-declared class as the default of a
// type parameter elaborates. The default is parsed into `typedef_type` rather
// than into an expression, which is why the expression walk that reports the
// restriction never reaches it.
TEST(ClassScopeResolutionElaboration,
     ForwardTypePrefixInTypeParamAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("module box;\n"
             "  typedef class Packet;\n"
             "  class Packet;\n"
             "    typedef shortint stamp_t;\n"
             "  endclass\n"
             "  localparam type stamp_alias_t = Packet::stamp_t;\n"
             "endmodule\n"));
}

// §6.18: a forward-declared name completed by something other than a class
// cannot carry a scope-resolution prefix at all, whichever context the prefix
// stands in. That report belongs to §6.18 and is the neighbour of the §8.23
// check: a typedef declaration is a permitted §8.23 context, so the source
// below must still be rejected, and by §6.18.
TEST(ClassScopeResolutionElaboration, NonClassForwardPrefixInTypedefIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module w;\n"
      "  typedef pkt_fwd;\n"
      "  typedef byte pkt_fwd;\n"
      "  typedef pkt_fwd::Field field_t;\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(f, "scope-resolution prefix");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.18");
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

// §8.23: a class-scoped parameter is a constant expression. Referencing it via
// `Class::PARAM` in a constant context must fold to the parameter's value at
// elaboration, not merely elaborate without error. Cfg::WIDTH resolves to 8.
TEST(ClassScopeResolutionElaboration, ClassParameterFoldsAsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int W = Cfg::WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "W");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 8);
}

// §8.23: a class-scoped local parameter is likewise a constant expression
// reachable through `::`. Cfg::DEPTH resolves to 16.
TEST(ClassScopeResolutionElaboration, ClassLocalparamFoldsAsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  localparam int DEPTH = 16;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int D = Cfg::DEPTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "D");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 16);
}

}  // namespace
