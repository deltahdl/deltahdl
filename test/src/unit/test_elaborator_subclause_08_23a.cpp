#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'T' may prefix the class scope resolution operator", 7,
      "6.20.3"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'T' may prefix the class scope resolution operator", 4,
      "6.20.3"));
}

TEST(ClassScopeResolutionElaboration, IncompleteForwardTypePrefixIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type 'my_data_t' defined by an interface-based typedef", 7, "8.23"));
}

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

TEST(ClassScopeResolutionElaboration, NonClassForwardPrefixInTypedefIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module w;\n"
      "  typedef pkt_fwd;\n"
      "  typedef byte pkt_fwd;\n"
      "  typedef pkt_fwd::Field field_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "scope-resolution prefix", 4,
                            "6.18"));
}

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

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInDataDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  C::T x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    3, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     InterfaceBasedTypedefPrefixInDataDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.data_t my_data_t;\n"
      "  my_data_t::Field x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type 'my_data_t' defined by an interface-based typedef", 6, "8.23"));
}

TEST(ClassScopeResolutionElaboration, TypeParamPrefixInClassPropertyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class P #(type C);\n"
      "  C::T x;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'C' may prefix the class scope resolution operator", 2,
      "6.20.3"));
}

TEST(ClassScopeResolutionElaboration,
     ClassPropertyThroughTypeParamAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class P #(type C);\n"
             "  localparam type C_t = C::T;\n"
             "  C_t y;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration,
     NonClassForwardPrefixInTypeParamAssignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module w;\n"
      "  typedef pkt_fwd;\n"
      "  typedef byte pkt_fwd;\n"
      "  localparam type field_t = pkt_fwd::Field;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "scope-resolution prefix 'pkt_fwd' of a type parameter assignment", 4,
      "6.18"));
}

TEST(ClassScopeResolutionElaboration, ScopedTypedefSizesFromTheNamedClass) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  typedef byte my_type;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

TEST(ClassScopeResolutionElaboration, ScopedTypedefSizesWithNoUnqualifiedName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForkArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial fork\n"
      "    x = C::val;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForInitializationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = C::val; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForStepIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; x = C::val) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial assert (1) x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial assert (1) else x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInRandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : x = C::val;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    6, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = C::val; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    6, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     ScopedTypedefFromAModuleLocalClassSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class Cfg;\n"
      "    typedef int my_type;\n"
      "  endclass\n"
      "  typedef byte my_type;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

TEST(ClassScopeResolutionElaboration,
     ScopedTypedefFromAModuleLocalClassSignsTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class Cfg;\n"
      "    typedef byte my_type;\n"
      "  endclass\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 8u);
  EXPECT_TRUE(x->is_signed);
}

TEST(ClassScopeResolutionElaboration,
     ScopedTypedefFromAModuleLocalClassSizesTheNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class Cfg;\n"
      "    typedef logic [7:0] beat_t;\n"
      "  endclass\n"
      "  wire Cfg::beat_t w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 8u);
}

TEST(ClassScopeResolutionElaboration, ScopedTypedefNamingNoSuchTypeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class Cfg;\n"
      "    typedef int my_type;\n"
      "  endclass\n"
      "  Cfg::absent_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'Cfg' declares no type 'absent_t'", 5,
                            "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     NestedClassUnqualifiedWriteToOuterNonStaticPropertyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  class Inner;\n"
      "    function void f();\n"
      "      outerProp = 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-static property 'outerProp' of the enclosing "
                            "class 'Outer'",
                            5, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     NestedClassUnqualifiedReadOfOuterNonStaticPropertyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  class Inner;\n"
      "    function int f();\n"
      "      return outerProp + 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-static property 'outerProp' of the enclosing "
                            "class 'Outer'",
                            5, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     NestedClassReadsOuterStaticPropertyUnqualified) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  static int outerStaticProp;\n"
      "  class Inner;\n"
      "    function int f();\n"
      "      outerStaticProp = 0;\n"
      "      return outerStaticProp;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindDiag(f, "outerStaticProp"), nullptr);
}

TEST(ClassScopeResolutionElaboration,
     NestedClassOwnPropertyShadowsOuterNonStaticProperty) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  class Inner;\n"
      "    int outerProp;\n"
      "    function void f();\n"
      "      outerProp = 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindDiag(f, "outerProp"), nullptr);
}

TEST(ClassScopeResolutionElaboration,
     NestedClassFormalAndLocalShadowOuterNonStaticProperty) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  int other;\n"
      "  class Inner;\n"
      "    function int f(int outerProp);\n"
      "      outerProp = 0;\n"
      "      begin\n"
      "        int other;\n"
      "        other = outerProp;\n"
      "        return other;\n"
      "      end\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindDiag(f, "enclosing class"), nullptr);
}

}  // namespace
