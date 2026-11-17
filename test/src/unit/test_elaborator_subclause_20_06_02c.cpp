#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InterfaceClassMessage(const char* name) {
  return std::string(
             "'$bits' shall not be applied to interface class object '") +
         name + "'";
}

TEST(BitsRestrictions,
     DISABLED_AnInterfaceClassHandleInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IC;\n"
      "endclass\n"
      "class Plain;\n"
      "endclass\n"
      "class Holder;\n"
      "  IC h;\n"
      "  Plain p;\n"
      "  function int width();\n"
      "    IC l;\n"
      "    return $bits(h) + $bits(l) + $bits(p);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), InterfaceClassMessage("h"),
                            10, "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), InterfaceClassMessage("l"),
                            10, "20.6.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

std::string DynamicTypeMessage(const char* name) {
  return std::string(
             "'$bits' cannot be applied directly to dynamically sized "
             "type '") +
         name + "'";
}

TEST(BitsRestrictions, DISABLED_AnAssociativeArrayTypedefIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef byte ai[int];\n"
      "  typedef byte as[string];\n"
      "  typedef byte aw[*];\n"
      "  typedef byte fx[4];\n"
      "  int a, b, c, d;\n"
      "  initial begin\n"
      "    a = $bits(ai);\n"
      "    b = $bits(as);\n"
      "    c = $bits(aw);\n"
      "    d = $bits(fx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicTypeMessage("ai"), 8,
                            "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicTypeMessage("as"), 9,
                            "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicTypeMessage("aw"), 10,
                            "20.6.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(
    BitsRestrictions,
    DISABLED_ADynamicallySizedTypedefInAClassMethodOrPackageFunctionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef int qt[$];\n"
      "  typedef int ft[2];\n"
      "  function int w();\n"
      "    return $bits(qt) + $bits(ft);\n"
      "  endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  typedef int dt[];\n"
      "  function int w();\n"
      "    return $bits(dt);\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicTypeMessage("qt"), 5,
                            "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicTypeMessage("dt"), 11,
                            "20.6.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

std::string DynamicFunctionMessage(const char* name) {
  return std::string("'$bits' shall not enclose function '") + name +
         "' whose return type is dynamically sized";
}

TEST(BitsRestrictions,
     DISABLED_AFunctionReturningADynamicallySizedTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int dt[];\n"
      "  typedef int at[string];\n"
      "  function dt mkd();\n"
      "    return dt'{1};\n"
      "  endfunction\n"
      "  function at mka();\n"
      "    at r;\n"
      "    return r;\n"
      "  endfunction\n"
      "  function string mks();\n"
      "    return \"a\";\n"
      "  endfunction\n"
      "  function int mki();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int a, b, c, d;\n"
      "  initial begin\n"
      "    a = $bits(mkd());\n"
      "    b = $bits(mka());\n"
      "    c = $bits(mks());\n"
      "    d = $bits(mki());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("mkd"),
                            19, "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("mka"),
                            20, "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("mks"),
                            21, "20.6.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(
    BitsRestrictions,
    DISABLED_ADynamicallySizedCallInAClassOrToAMethodOrPackageFunctionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  function string ps();\n"
      "    return \"a\";\n"
      "  endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  typedef int qt[$];\n"
      "  function qt mq();\n"
      "    return {};\n"
      "  endfunction\n"
      "  static function string ms();\n"
      "    return \"a\";\n"
      "  endfunction\n"
      "  function int w();\n"
      "    return $bits(mq());\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $bits(C::ms());\n"
      "    b = $bits(pk::ps());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("mq"),
                            15, "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("ms"),
                            21, "20.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicFunctionMessage("ps"),
                            22, "20.6.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(BitsArguments, DISABLED_NoArgumentOrTwoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = $bits();\n"
      "    y = $bits(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "$bits takes exactly one argument", line,
                              "20.6.2"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(BitsArguments, OneExpressionOrOneTypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [3:0] a;\n"
             "  int x, y;\n"
             "  initial begin\n"
             "    x = $bits(a);\n"
             "    y = $bits(logic [7:0]);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BitsConstant, DISABLED_AConversionFunctionsResultIsAConstantSize) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = $bits($realtobits(1.0));\n"
      "  localparam int B = $bits($bitstoreal(64'h0));\n"
      "  localparam int C = $bits($shortrealtobits(1.0));\n"
      "  localparam int D = $bits($bitstoshortreal(32'h0));\n"
      "  localparam int E = $bits($rtoi(1.0));\n"
      "  logic [$bits($realtobits(1.0)) - 1 : 0] v;\n"
      "  localparam int V = $bits(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "A"), 64);
  EXPECT_EQ(ParamValue(design, "B"), 64);
  EXPECT_EQ(ParamValue(design, "C"), 32);
  EXPECT_EQ(ParamValue(design, "D"), 32);
  EXPECT_EQ(ParamValue(design, "E"), 32);
  EXPECT_EQ(ParamValue(design, "V"), 64);
}

TEST(BitsConstant, DISABLED_AClassSpecializationTakesBitsAsItsValueArgument) {
  EXPECT_TRUE(
      ElabOk("class K;\n"
             "  typedef byte inner;\n"
             "endclass\n"
             "class Y #(int P = 0);\n"
             "endclass\n"
             "typedef byte bt;\n"
             "module top #(type T = K);\n"
             "  Y #($bits(type(K::inner))) y1;\n"
             "  Y #($bits(type(bt))) y2;\n"
             "  Y #($bits(T)) y3;\n"
             "  Y #($bits(K::inner)) y4;\n"
             "endmodule\n"));
}

}  // namespace
