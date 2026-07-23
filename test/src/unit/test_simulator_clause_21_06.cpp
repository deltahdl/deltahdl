// §21.6 Command line input — plusargs supplied on the simulation invocation
// (leading '+' stripped) are queried by two system functions:
//   $test$plusargs(string): scans the plusargs in the order supplied and
//     returns a nonzero integer when the prefix of one of them matches every
//     character of the provided string, zero otherwise. The string is given
//     as a literal or as a variable read back as text (leading nulls dropped,
//     no leading '+').
//   $value$plusargs(user_string, variable): same search over the
//     plusarg_string portion of "plusarg_string format_string"; the first
//     matching plusarg's remainder is converted per the format (%d %o %h/%x
//     %b %e %f %g %s, upper/lower/leading-0 forms) and stored in the
//     variable. No match: returns zero, variable untouched, no warning. An
//     empty remainder stores zero / the empty string; a too-wide value is
//     truncated (a negative value counts as too wide); characters illegal for
//     the conversion store 'bx.
//
// Every conversion's behavior depends on how the destination (or pattern)
// variable is declared — integer, packed vector, real, string — so each test
// declares its variables with real syntax and drives the module through the
// full pipeline, injecting the invocation's plusargs through the production
// intake API (SimContext::AddPlusArg) before the run and observing $display
// output.
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout. Plusargs for the run are
// added to f.ctx beforehand — the in-simulator image of the invocation's
// +arguments.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// ---------------------------------------------------------------------------
// $test$plusargs
// ---------------------------------------------------------------------------

// §21.6: the first LRM example — with +HELLO supplied, every pattern that is
// a prefix-complete match ("HELLO", "HE", "H") succeeds, while a pattern
// longer than the plusarg ("HELLO_HERE") or diverging from it ("HI", "LO")
// returns zero. Calls sit in if-condition position.
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

// §21.6: the plusargs are searched in the order provided — an earlier
// non-matching plusarg is skipped and a later one still matches.
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

// §21.6: the search string may come from an integral variable interpreted as
// text; the leading null bytes of the padded vector are ignored and are not
// part of the matching string. The pattern variable is built by a real
// declaration plus procedural assignment.
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

// §21.6: a string-typed variable also supplies the search string; here it is
// built with a declaration initializer.
TEST(TestPlusargsSim, PatternFromStringVariable) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    string s = \"HEL\";\n"
      "    if ($test$plusargs(s)) $display(\"string pattern found\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "string pattern found\n");
}

// §21.6 negative: the provided string shall not include the leading '+' of
// the command-line argument — a pattern spelled with the '+' matches nothing.
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

// §21.6: the function returns an integer — nonzero on a match, zero
// otherwise — usable in assignment and expression positions, not just as an
// if-condition.
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

// §21.6: the query works the same from a task body — the plusarg list belongs
// to the invocation, not to any one process or scope.
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

// §21.6: a parameter or localparam holding the pattern text is a constant
// form of the string operand — resolved at elaboration rather than read from
// a variable at run time, so it exercises the constant path into the same
// search. (Patterns kept within 32 bits: an untyped parameter set from a
// longer string literal is truncated to 32 bits by an upstream defect in
// parameter sizing, outside this clause.)
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

// ---------------------------------------------------------------------------
// $value$plusargs
// ---------------------------------------------------------------------------

// §21.6: the decimal branch of the second LRM example — +TEST=5 matches
// "TEST=%d" and the remainder converts into the integer variable.
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

// §21.6: with no matching plusarg the function returns zero, the variable
// keeps its prior value, and no warning is generated.
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

// §21.6: the first plusarg in command-line order whose prefix matches is the
// one converted; a non-matching earlier arg is skipped and a later duplicate
// is ignored.
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

// §21.6: the user_string may come from a variable holding the pattern text —
// the third branch of the second LRM example. With +TEST=5, the pattern
// "TEST%d" leaves the remainder "=5", whose '=' is illegal for the decimal
// conversion, so the variable is written with 'bx.
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

// §21.6: with +TEST23 the same variable pattern's remainder "23" is all legal
// decimal digits and converts normally — the last branch of the LRM example.
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

// §21.6: %s stores the remainder characters unconverted into a packed vector,
// right-justified with zero padding above — so the vector compares equal to
// the corresponding string literal.
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

// §21.6: the middle branch of the second LRM example — %0F (uppercase with a
// leading 0) is a valid spelling of the real conversion, '+' inside the
// plusarg body is ordinary text, and the negated call selects the default
// assignment when conversion succeeded is false.
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

// §21.6: same source with no +FREQ plusarg — the function returns zero, the
// real variable is not modified by the call, and the else-path default wins.
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

// §21.6: %e is the exponential spelling of the real conversion; scientific
// notation in the remainder converts to the same real value.
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

// §21.6: a string-typed destination takes exactly the remainder text.
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

// §21.6: when no string remains after the matched prefix, a string
// destination receives the empty string.
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

// §21.6: when no string remains after the matched prefix, a numeric
// destination receives zero — overwriting its prior value.
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

// §21.6: a variable wider than the converted value is zero-padded up to its
// width.
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

// §21.6: a variable that cannot contain the converted value keeps only the
// low-order part — the value is truncated to the variable width. Uppercase
// hex digits are legal for %h.
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

// §21.6: a negative value is considered larger than the variable provided —
// its two's-complement image is truncated to the destination width.
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

// §21.6: the binary conversion admits the 4-state digit characters — each
// x or z in the remainder lands in the corresponding bit of the destination.
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

// §21.6: an x digit in a hex remainder yields a whole unknown nibble beside
// the known one.
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

// §21.6: underscores after the first digit are digit separators, not illegal
// characters, for the numeric conversions.
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

// §21.6: a decimal remainder that is the single character x stands for a
// wholly unknown value.
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

// §21.6: %o is the octal member of the valid conversion set.
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

// §21.6: %x is the alternative spelling of the hexadecimal conversion, and
// uppercase remainder digits are legal for it.
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

// §21.6: %g is the third real-conversion spelling.
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

// §21.6: the user_string may also come from a string-typed variable — the
// same pattern-source rule $test$plusargs has, exercised on $value$plusargs's
// own search path.
TEST(ValuePlusargsSim, UserStringFromStringVariable) {
  SimFixture f;
  f.ctx.AddPlusArg("MODE=3");
  std::string out = RunCapture(
      "module t;\n"
      "  int mode;\n"
      "  initial begin\n"
      "    string us = \"MODE=%d\";\n"
      "    if ($value$plusargs(us, mode)) $display(\"mode=%0d\", mode);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "mode=3\n");
}

// §21.6 negative: the plusarg_string of $value$plusargs shall not include the
// leading '+' either — spelled with it, nothing matches and the destination
// keeps its prior value.
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

// §21.6 negative: a conversion outside the valid set (%c is not among
// %d/%o/%h/%x/%b/%e/%f/%g/%s) can convert no character legally, so on a
// prefix match the destination is written with 'bx.
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

// §21.6 negative: a character illegal for the binary conversion ('2') writes
// the whole destination with 'bx even though other characters were legal.
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

}  // namespace
