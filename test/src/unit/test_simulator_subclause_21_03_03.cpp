#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringFormatTaskSim, SwriteWritesToStringVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s, \"x=%0d y=%0d\", 7, 11);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x=7 y=11\n");
}

TEST(StringFormatTaskSim, SwriteSuffixSelectsRadix) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] h;\n"
      "  logic [7:0] o;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    h = 8'hab; o = 8'o17; b = 4'b1010;\n"
      "    $swriteh(s, h); $display(\"%s\", s);\n"
      "    $swriteo(s, o); $display(\"%s\", s);\n"
      "    $swriteb(s, b); $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ab\n017\n1010\n");
}

TEST(StringFormatTaskSim, SformatUsesSecondArgAsFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"data is %0d\", 123);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "data is 123\n");
}

TEST(StringFormatTaskSim, SformatLaterStringArgIsNotFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"tag=%s\", \"raw %d nope\");\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "tag=raw %d nope\n");
}

TEST(StringFormatTaskSim, SformatFormatArgFromStringVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"n=%0d\";\n"
      "    $sformat(s, fmt, 9);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=9\n");
}

TEST(StringFormatTaskSim, SformatSupportsCharacterSpecifier) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"ch=%c\", 65);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ch=A\n");
}

TEST(StringFormatTaskSim, SformatConsumesArgsInOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"a=%0d, b=%s, c=%0d\", 1, \"two\", 3);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=1, b=two, c=3\n");
}

TEST(StringFormatTaskSim, SformatfReturnsFormattedResult) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = $sformatf(\"val=%0d\", 42);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "val=42\n");
}

TEST(StringFormatTaskSim, SwriteByteOrderingIntoExactWidthVector) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  initial begin\n"
      "    $swrite(v, \"ABCD\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "41424344\n");
}

TEST(StringFormatTaskSim, SwriteTruncatesNarrowerDestination) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  initial begin\n"
      "    $swrite(v, \"ABCD\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4344\n");
}

TEST(StringFormatTaskSim, SformatRightJustifiesWiderDestination) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  initial begin\n"
      "    $sformat(v, \"AB\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "00004142\n");
}

TEST(StringFormatTaskSim, SformatArgCountMismatchWarnsAndContinues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"a=%0d b=%0d\", 1);\n"
      "    $display(\"done %s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
  EXPECT_NE(out.find("done "), std::string::npos);
}

TEST(StringFormatTaskSim, SwriteIntoUnpackedByteArrayLeftToRight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [0:3];\n"
      "  initial begin\n"
      "    $swrite(b, \"ABCD\");\n"
      "    $display(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ABCD\n");
}

TEST(StringFormatTaskSim, SformatIntoUnpackedByteArrayPadsRemainder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [0:3];\n"
      "  initial begin\n"
      "    $sformat(b, \"v%0d\", 7);\n"
      "    $display(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v7\n");
}

TEST(StringFormatTaskSim, SwriteBareExpressionRendersDecimal) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd255;\n"
      "    $swrite(s, v);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "255\n");
}

TEST(StringFormatTaskSim, SwriteIntoDescendingUnpackedByteArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [3:0];\n"
      "  initial begin\n"
      "    $swrite(b, \"ABCD\");\n"
      "    $display(\"%c%c%c%c\", b[0], b[1], b[2], b[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "DCBA\n");
}

TEST(StringFormatTaskSim, SformatFormatArgFromIntegralExpression) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [39:0] fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"n=%0d\";\n"
      "    $sformat(s, fmt, 5);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=5\n");
}

TEST(StringFormatTaskSim, SformatFormatArgFromByteArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte fmt [0:3];\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt[0] = \"%\"; fmt[1] = \"0\"; fmt[2] = \"d\"; fmt[3] = \"!\";\n"
      "    $sformat(s, fmt, 5);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5!\n");
}

TEST(StringFormatTaskSim, SformatTooManyArgsWarnsAndContinues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"only=%0d\", 1, 2, 3);\n"
      "    $display(\"done %s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
  EXPECT_NE(out.find("done only=1"), std::string::npos);
}

TEST(StringFormatTaskSim, SformatfUsableAsExpressionArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%s\", $sformatf(\"val=%0d\", 42));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "val=42\n");
}

TEST(StringFormatTaskSim, ArgCountMismatchWarningNames21_3_3) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial $sformat(s, \"x=%0d y=%0d\", 4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "does not match supplied argument count", 3,
                              "21.3.3"));
}

TEST(StringFormatTaskSim, SformatDestinationWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [8*8:1] s;\n"
      "  integer hits;\n"
      "  always @(s) hits = hits + 1;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    #1 $sformat(s, \"%0d\", 42);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringFormatTaskSim, SformatfResultDisplaysAsText) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int v = 5;\n"
      "  initial $display($sformatf(\"e %0d\", v));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "e 5\n");
}

TEST(StringFormatTaskSim, SformatfAndSformatFormatAggregatesWithP) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed {logic [3:0] hi; logic [3:0] lo;} ps_t;\n"
      "  typedef struct {int a; int b;} us_t;\n"
      "  ps_t v = '{hi:5, lo:6};\n"
      "  us_t u = '{1, 2};\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = $sformatf(\"%p\", v);\n"
      "    $display(s);\n"
      "    $sformat(s, \"<%p>\", u);\n"
      "    $display(s);\n"
      "    s = $sformatf(\"%4b|%e|%c|%0d%%\", 4'd5, 1.5, 90, 100);\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{hi:5, lo:6}\n<'{a:1, b:2}>\n0101|1.500000e+00|Z|100%\n");
}

TEST(StringFormatTaskSim, StringMethodsOnSformatfResult) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s = \"abcd\";\n"
      "  initial begin\n"
      "    $display(\"%0d\", $sformatf(\"%s\", s).len());\n"
      "    $display(\"%s\", $sformatf(\"x%sy\", s).substr(1, 2).toupper());\n"
      "    $display(\"%0d\", $sformatf(\"%0d\", 12345).atoi() + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\nAB\n12346\n");
}

TEST(StringFormatTaskSim, SformatfResultPrintsAsTextWhateverItsFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C; string f = \"k=%0d\"; endclass\n"
      "  C c = new;\n"
      "  string fmt = \"m=%0d\";\n"
      "  initial begin\n"
      "    $display($sformatf(fmt, 4));\n"
      "    $display($sformatf(c.f, 5));\n"
      "    $display($sformatf(\"outer(%s)\", $sformatf(\"inner %0d\", 9)));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "m=4\nk=5\nouter(inner 9)\n");
}

TEST(StringFormatTaskSim, SwriteAndSformatWriteClassProperties) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    string s;\n"
      "    logic [31:0] w;\n"
      "    function void fill; $swrite(s, \"v=%0d s=%s\", 5, \"ab\"); "
      "endfunction\n"
      "  endclass\n"
      "  C c = new, d = new;\n"
      "  initial begin\n"
      "    c.fill();\n"
      "    $display(c.s);\n"
      "    $swrite(d.s, \"h=%0d\", 12);\n"
      "    $sformat(d.w, \"%s\", \"ab\");\n"
      "    $display(\"[%s] %h\", d.s, d.w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v=5 s=ab\n[h=12] 00006162\n");
}

}  // namespace
