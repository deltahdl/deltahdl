#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

// Full pipeline including the preprocessor. The default units_number (Table
// 20-3) is the smallest time precision of the `timescale directives, which the
// preprocessor -> elaborator -> lowerer chain resolves into the simulation
// time precision; the plain sim fixture skips the preprocessor, so drive it
// explicitly here.
RtlirDesign* PreprocElaborate(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  // What a `timescale directive said is read by the preprocessor and consumed
  // by the elaborator, but the two never meet: the parser is handed a token
  // stream, so the caller that ran both has to carry the value across, as the
  // driver does. Without this the compilation unit reports no timescale and
  // the elaborator falls back to its ns default.
  cu->preproc_timescale = preproc.CurrentTimescale();
  cu->has_preproc_timescale = preproc.HasTimescale();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// §20.4.3: a $timeformat call sets the time unit, precision number, suffix
// string, and minimum field width for %t. A following $display("%t", ...)
// renders the value with the configured decimal precision, tags it with the
// suffix, and left-pads it to the minimum field width. Without the format being
// wired through to %t the task would print only the raw integer, so the exact
// spacing and suffix here observe the installed configuration end to end.
//
// The precision here is 2 because that is the top of the range §20.4.3 gives
// for the argument, from 2 to -15; anything above it is the rejection
// PrecisionAboveRangeRejected covers, which would leave the Table 20-3 defaults
// in place and make this a test of those instead.
//
// §20.4.3's own worked example passes a precision_number of 5 and prints five
// fractional digits, so the clause contradicts itself and this test looks wrong
// against the example. It is not: deltahdl follows the "shall" sentence, which
// is the decision recorded on #2867. Raising this argument to match the example
// is a change to that decision and to TimeformatRangeOk in
// src/simulator/eval_system_func.cpp, not a correction to this test.
TEST(TimeformatSysTask, InstalledFormatAppliesToPercentT) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 10);\n"
      "    $display(\"%t\", 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  // "5.00" (4) + " ns" (3) = 7 chars, padded with 3 leading spaces to
  // width 10.
  EXPECT_EQ(out, "   5.00 ns\n");
}

// Table 20-3: with no $timeformat call the defaults apply -- precision 0 (no
// fractional digits), a null suffix string, and a minimum field width of 20. A
// bare %t value is therefore right-justified in a 20-column field with nothing
// appended.
TEST(TimeformatSysTask, DefaultFormatPadsToTwentyColumns) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%t]\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[" + std::string(19, ' ') + "3]\n");
}

// §20.4.3: the configuration persists "for all %t formats in the design until
// another $timeformat system task is invoked", so a single call governs every
// later %t rendering, not just the next one.
TEST(TimeformatSysTask, FormatPersistsAcrossDisplays) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 1, \"ns\", 0);\n"
      "    $display(\"%t\", 4);\n"
      "    $display(\"%t\", 6);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4.0ns\n6.0ns\n");
}

// §20.4.3: a later $timeformat replaces the configuration; the same raw value
// then renders with the new precision and suffix.
TEST(TimeformatSysTask, ReinvocationReplacesFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 1, \"ns\", 0);\n"
      "    $display(\"%t\", 4);\n"
      "    $timeformat(-12, 2, \"ps\", 0);\n"
      "    $display(\"%t\", 8);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4.0ns\n8.00ps\n");
}

// Table 20-3, first row: the default units_number is the smallest time
// precision of all `timescale directives in the design. A design timescaled to
// 1 ps precision therefore seeds a default units_number of -12 (Table 20-2)
// when no $timeformat has run.
TEST(TimeformatSysTask, DefaultUnitsFollowSmallestTimescalePrecision) {
  SimFixture f;
  auto* design = PreprocElaborate(
      "`timescale 10ns / 1ps\n"
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.GetTimeFormat().units_number, -12);
}

// §20.4.3 shall: units_number is an integer in the Table 20-2 range from 2 to
// -15. A units_number above the range (3) is rejected with a diagnostic.
TEST(TimeformatSysTask, UnitsAboveRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(3, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §20.4.3 shall: a units_number below -15 is likewise rejected.
TEST(TimeformatSysTask, UnitsBelowRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-16, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §20.4.3 shall: precision_number carries the same Table 20-2 range constraint;
// a precision below -15 is rejected.
TEST(TimeformatSysTask, PrecisionBelowRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-9, -16, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §20.4.3 shall (upper boundary of the precision argument): a precision_number
// above 2 is out of the Table 20-2 range and is likewise rejected. This is the
// negative form at the opposite boundary from the below-range case, and on the
// precision argument rather than the units argument.
TEST(TimeformatSysTask, PrecisionAboveRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-9, 3, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The Table 20-2 range is closed: the endpoints 2 and -15 are valid inputs for
// units_number and precision_number and shall not raise a diagnostic.
TEST(TimeformatSysTask, RangeEndpointsAccepted) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(2, -15, \"\", 0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §20.4.3 shall (error path): when a $timeformat argument is out of range the
// call is rejected and the previously installed configuration is left intact,
// so a later %t still renders under the earlier, valid format.
TEST(TimeformatSysTask, OutOfRangeLeavesPriorFormatIntact) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \"ns\", 0);\n"
      "    $timeformat(5, 0, \"XX\", 0);\n"
      "    $display(\"%t\", 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_NE(out.find("7.00ns"), std::string::npos);
  // The rejected call's suffix must not have leaked into the configuration.
  EXPECT_EQ(out.find("XX"), std::string::npos);
}

// Syntax 20-5: the argument block is optional. A bare $timeformat leaves the
// current configuration untouched, so a %t after it still uses the format
// installed by the earlier full invocation.
TEST(TimeformatSysTask, BareInvocationLeavesFormatUnchanged) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \"ns\", 0);\n"
      "    $timeformat;\n"
      "    $display(\"%t\", 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3.00ns\n");
}

// §20.4.3: the configuration governs %t not only in the display tasks of §21.2
// but also in the file-output tasks of §21.3. Driven end to end -- the file
// descriptor comes from a real $fopen and the text is written by a real
// $fdisplay to that file -- and observed by reading the file back. This is the
// same task family the subclause's own example exercises with $fmonitor.
TEST(TimeformatSysTask, FileOutputTaskAppliesFormat) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_tf_20_04_03_file.txt";
  std::remove(kPath.c_str());
  RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 0);\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fdisplay(fd, \"%t\", 5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(kPath), "5.00 ns\n");
  std::remove(kPath.c_str());
}

// §20.4.3: the configuration also governs %t in the formatting system function
// $sformatf (§21.3.3). The returned string carries the configured precision and
// suffix, observed here by displaying it.
TEST(TimeformatSysTask, FormattedStringFunctionAppliesFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \"ns\", 0);\n"
      "    $display(\"%s\", $sformatf(\"%t\", 6));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("6.00ns"), std::string::npos);
}

// §20.4.3: the units number and precision number arguments shall be integers
// in the range 2 to -15, and the report that rejects one names §20.4.3.
TEST(TimeformatSysTask, OutOfRangeArgumentNames20_4_3) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(4, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  const Diagnostic* d = FindDiag(f, "out of range [2 .. -15]");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "20.4.3");
}

}  // namespace
