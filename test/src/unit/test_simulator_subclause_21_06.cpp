#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"

using namespace delta;

namespace {

TEST(TestPlusargsSim, LrmPrefixMatchExample) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    if ($test$plusargs(\"HELLO\")) $display(\"Hello argument "
      "found.\");\n"
      "    if ($test$plusargs(\"HE\")) $display(\"The HE subset string is "
      "detected.\");\n"
      "    if ($test$plusargs(\"H\")) $display(\"Argument starting with H "
      "found.\");\n"
      "    if ($test$plusargs(\"HELLO_HERE\")) $display(\"Long argument.\");\n"
      "    if ($test$plusargs(\"HI\")) $display(\"Simple greeting.\");\n"
      "    if ($test$plusargs(\"LO\")) $display(\"Does not match.\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "Hello argument found.\n"
            "The HE subset string is detected.\n"
            "Argument starting with H found.\n");
}

TEST(TestPlusargsSim, SearchScansAllArgsInOrder) {
  SimFixture f;
  f.ctx.AddPlusArg("FOO");
  f.ctx.AddPlusArg("BAR=baz");
  std::string out = RunCapture(
      "module t;\n"
      "  initial if ($test$plusargs(\"BAR\")) $display(\"bar seen\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "bar seen\n");
}

TEST(TestPlusargsSim, PatternFromVectorVariableIgnoresLeadingNulls) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [8*8:1] pat;\n"
      "  initial begin\n"
      "    pat = \"HE\";\n"
      "    if ($test$plusargs(pat)) $display(\"var pattern found\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "var pattern found\n");
}

TEST(TestPlusargsSim, PatternFromStringVariable) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    static string s = \"HEL\";\n"
      "    if ($test$plusargs(s)) $display(\"string pattern found\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "string pattern found\n");
}

TEST(TestPlusargsSim, PatternWithLeadingPlusDoesNotMatch) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    if ($test$plusargs(\"+HELLO\")) $display(\"plus matched\");\n"
      "    else $display(\"plus rejected\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "plus rejected\n");
}

TEST(TestPlusargsSim, ReturnsNonzeroIntegerOnMatchZeroOtherwise) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = $test$plusargs(\"HELLO\");\n"
      "    if (r != 0) $display(\"hit nonzero\");\n"
      "    r = $test$plusargs(\"NOPE\");\n"
      "    $display(\"miss %0d\", r);\n"
      "    $display(\"expr %0d\", $test$plusargs(\"NOPE\") + 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hit nonzero\nmiss 0\nexpr 0\n");
}

TEST(TestPlusargsSim, QueryFromTaskBody) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  task check;\n"
      "    if ($test$plusargs(\"HELLO\")) $display(\"task sees it\");\n"
      "  endtask\n"
      "  initial check;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "task sees it\n");
}

TEST(TestPlusargsSim, PatternFromParameterConstant) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  parameter PAT = \"HE\";\n"
      "  localparam LPAT = \"HELL\";\n"
      "  initial begin\n"
      "    if ($test$plusargs(PAT)) $display(\"param pattern found\");\n"
      "    if ($test$plusargs(LPAT)) $display(\"localparam pattern found\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "param pattern found\nlocalparam pattern found\n");
}

TEST(ValuePlusargsSim, DecimalConversionIntoInteger) {
  SimFixture f;
  f.ctx.AddPlusArg("TEST=5");
  std::string out = RunCapture(
      "module t;\n"
      "  integer i1;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"TEST=%d\", i1))\n"
      "      $display(\"value was %0d\", i1);\n"
      "    else\n"
      "      $display(\"+TEST= not found\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "value was 5\n");
}

TEST(ValuePlusargsSim, NoMatchLeavesVariableAndIssuesNoWarning) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer i1;\n"
      "  initial begin\n"
      "    i1 = 42;\n"
      "    if ($value$plusargs(\"TEST=%d\", i1))\n"
      "      $display(\"value was %0d\", i1);\n"
      "    else\n"
      "      $display(\"+TEST= not found, still %0d\", i1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "+TEST= not found, still 42\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(ValuePlusargsSim, FirstMatchingPlusargSuppliesTheValue) {
  SimFixture f;
  f.ctx.AddPlusArg("OTHER=1");
  f.ctx.AddPlusArg("VAL=7");
  f.ctx.AddPlusArg("VAL=9");
  std::string out = RunCapture(
      "module t;\n"
      "  int v;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"VAL=%d\", v)) $display(\"v=%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v=7\n");
}

TEST(ValuePlusargsSim, PatternFromVectorVariableAndIllegalCharStoresX) {
  SimFixture f;
  f.ctx.AddPlusArg("TEST=5");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [64*8:1] pstring;\n"
      "  logic [8*32:1] testname;\n"
      "  initial begin\n"
      "    pstring = \"TEST%d\";\n"
      "    if ($value$plusargs(pstring, testname))\n"
      "      $display(\"Running test number %0d.\", testname);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Running test number x.\n");
}

TEST(ValuePlusargsSim, VariablePatternTrailingDigitsConvert) {
  SimFixture f;
  f.ctx.AddPlusArg("TEST23");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [64*8:1] pstring;\n"
      "  logic [8*32:1] testname;\n"
      "  initial begin\n"
      "    pstring = \"TEST%d\";\n"
      "    if ($value$plusargs(pstring, testname))\n"
      "      $display(\"Running test number %0d.\", testname);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Running test number 23.\n");
}

TEST(ValuePlusargsSim, StringConversionIntoPackedVector) {
  SimFixture f;
  f.ctx.AddPlusArg("TESTNAME=t1");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [8*32:1] testname;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"TESTNAME=%s\", testname)) begin\n"
      "      $display(\"TESTNAME= %0s.\", testname);\n"
      "      if (testname == \"t1\") $display(\"padded compare ok\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "TESTNAME= t1.\npadded compare ok\n");
}

TEST(ValuePlusargsSim, RealConversionUppercaseLeadingZeroForm) {
  SimFixture f;
  f.ctx.AddPlusArg("FREQ+9.234");
  std::string out = RunCapture(
      "module t;\n"
      "  real frequency;\n"
      "  initial begin\n"
      "    if (!($value$plusargs(\"FREQ+%0F\", frequency)))\n"
      "      frequency = 8.33333;\n"
      "    $display(\"frequency = %f\", frequency);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "frequency = 9.234000\n");
}

TEST(ValuePlusargsSim, RealDefaultAppliedWhenPlusargAbsent) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real frequency;\n"
      "  initial begin\n"
      "    if (!($value$plusargs(\"FREQ+%0F\", frequency)))\n"
      "      frequency = 8.33333;\n"
      "    $display(\"frequency = %f\", frequency);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "frequency = 8.333330\n");
}

TEST(ValuePlusargsSim, ExponentialRealConversion) {
  SimFixture f;
  f.ctx.AddPlusArg("RATE=2.5e1");
  std::string out = RunCapture(
      "module t;\n"
      "  real rate;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"RATE=%e\", rate))\n"
      "      $display(\"rate = %g\", rate);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "rate = 25\n");
}

TEST(ValuePlusargsSim, StringTypeDestinationHoldsRemainder) {
  SimFixture f;
  f.ctx.AddPlusArg("NAME=hi");
  std::string out = RunCapture(
      "module t;\n"
      "  string name;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"NAME=%s\", name))\n"
      "      $display(\"[%0s]\", name);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[hi]\n");
}

TEST(ValuePlusargsSim, EmptyRemainderStoresEmptyString) {
  SimFixture f;
  f.ctx.AddPlusArg("TAG=");
  std::string out = RunCapture(
      "module t;\n"
      "  string tag;\n"
      "  initial begin\n"
      "    tag = \"seed\";\n"
      "    if ($value$plusargs(\"TAG=%s\", tag))\n"
      "      $display(\"[%0s]\", tag);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
}

TEST(ValuePlusargsSim, EmptyRemainderStoresZeroNumeric) {
  SimFixture f;
  f.ctx.AddPlusArg("COUNT=");
  std::string out = RunCapture(
      "module t;\n"
      "  int count;\n"
      "  initial begin\n"
      "    count = 99;\n"
      "    if ($value$plusargs(\"COUNT=%d\", count))\n"
      "      $display(\"count=%0d\", count);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "count=0\n");
}

TEST(ValuePlusargsSim, WideDestinationZeroPadded) {
  SimFixture f;
  f.ctx.AddPlusArg("W=ff");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [63:0] w;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"W=%h\", w)) $display(\"w=%h\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "w=00000000000000ff\n");
}

TEST(ValuePlusargsSim, NarrowDestinationTruncates) {
  SimFixture f;
  f.ctx.AddPlusArg("V=1FF");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"V=%h\", v)) $display(\"v=%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v=ff\n");
}

TEST(ValuePlusargsSim, NegativeValueTruncatesToWidth) {
  SimFixture f;
  f.ctx.AddPlusArg("OFF=-1");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] off;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"OFF=%d\", off)) $display(\"off=%0d\", off);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "off=255\n");
}

TEST(ValuePlusargsSim, BinaryConversionKeepsFourStateDigits) {
  SimFixture f;
  f.ctx.AddPlusArg("BUS=1x0z");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] bus;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"BUS=%b\", bus)) $display(\"bus=%b\", bus);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "bus=1x0z\n");
}

TEST(ValuePlusargsSim, HexConversionKeepsFourStateDigit) {
  SimFixture f;
  f.ctx.AddPlusArg("A=xf");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"A=%h\", a)) $display(\"a=%h\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=xf\n");
}

TEST(ValuePlusargsSim, UnderscoreSeparatorAcceptedInDecimal) {
  SimFixture f;
  f.ctx.AddPlusArg("NUM=1_0");
  std::string out = RunCapture(
      "module t;\n"
      "  int num;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"NUM=%d\", num)) $display(\"num=%0d\", num);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=10\n");
}

TEST(ValuePlusargsSim, DecimalSingleXStoresAllUnknown) {
  SimFixture f;
  f.ctx.AddPlusArg("N=x");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"N=%d\", n)) $display(\"n=%b\", n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=xxxxxxxx\n");
}

TEST(ValuePlusargsSim, OctalConversion) {
  SimFixture f;
  f.ctx.AddPlusArg("PERM=17");
  std::string out = RunCapture(
      "module t;\n"
      "  int perm;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"PERM=%o\", perm)) $display(\"perm=%0d\", "
      "perm);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "perm=15\n");
}

TEST(ValuePlusargsSim, HexConversionXSpelling) {
  SimFixture f;
  f.ctx.AddPlusArg("ADDR=BEEF");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] addr;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"ADDR=%x\", addr)) $display(\"addr=%h\", "
      "addr);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "addr=beef\n");
}

TEST(ValuePlusargsSim, GeneralRealConversion) {
  SimFixture f;
  f.ctx.AddPlusArg("GAIN=0.25");
  std::string out = RunCapture(
      "module t;\n"
      "  real gain;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"GAIN=%g\", gain)) $display(\"gain=%g\", "
      "gain);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "gain=0.25\n");
}

TEST(ValuePlusargsSim, UserStringFromStringVariable) {
  SimFixture f;
  f.ctx.AddPlusArg("MODE=3");
  std::string out = RunCapture(
      "module t;\n"
      "  int mode;\n"
      "  initial begin\n"
      "    static string us = \"MODE=%d\";\n"
      "    if ($value$plusargs(us, mode)) $display(\"mode=%0d\", mode);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "mode=3\n");
}

TEST(ValuePlusargsSim, UserStringWithLeadingPlusDoesNotMatch) {
  SimFixture f;
  f.ctx.AddPlusArg("MODE=3");
  std::string out = RunCapture(
      "module t;\n"
      "  int mode;\n"
      "  initial begin\n"
      "    mode = 8;\n"
      "    if ($value$plusargs(\"+MODE=%d\", mode)) $display(\"matched\");\n"
      "    else $display(\"no match, still %0d\", mode);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "no match, still 8\n");
}

TEST(ValuePlusargsSim, InvalidConversionSpecStoresX) {
  SimFixture f;
  f.ctx.AddPlusArg("CH=a");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] ch;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"CH=%c\", ch)) $display(\"ch=%b\", ch);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ch=xxxxxxxx\n");
}

TEST(ValuePlusargsSim, IllegalBinaryCharStoresAllX) {
  SimFixture f;
  f.ctx.AddPlusArg("FLAG=12");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] flag;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"FLAG=%b\", flag)) $display(\"flag=%b\", "
      "flag);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "flag=xxxxxxxx\n");
}

TEST(ValuePlusargsSim, DestinationWakesAnEventControlOnIt) {
  SimFixture f;
  f.ctx.AddPlusArg("N=7");
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer v;\n"
      "  integer hits;\n"
      "  always @(v) hits = hits + 1;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    #1 $value$plusargs(\"N=%d\", v);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(PlusargCommandLine, PlusArgumentsReachThePlusargs) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"t.sv", "+HELLO", "+TEST=5"}, opts));
  EXPECT_EQ(opts.plus_args, (std::vector<std::string>{"HELLO", "TEST=5"}));
  EXPECT_EQ(opts.source_files, (std::vector<std::string>{"t.sv"}));
}

TEST(PlusargCommandLine, ToolPlusOptionsAreNotPlusargs) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"+define+W=8", "+incdir+inc", "+GO"}, opts));
  EXPECT_EQ(opts.plus_args, (std::vector<std::string>{"GO"}));
  ASSERT_EQ(opts.defines.size(), 1u);
  EXPECT_EQ(opts.defines[0].first, "W");
  EXPECT_EQ(opts.include_dirs, (std::vector<std::string>{"inc"}));
}

}  // namespace
