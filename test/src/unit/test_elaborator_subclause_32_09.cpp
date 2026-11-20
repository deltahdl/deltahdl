#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string CallerOf(const std::string& decls, const std::string& stmt) {
  return "module leaf;\n"
         "endmodule\n"
         "module top;\n"
         "  leaf a();\n" +
         decls + "  initial " + stmt +
         "\n"
         "endmodule\n";
}

void ExpectReportedOnTheCall(const std::string& src, const char* message) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "$sdf_annotate"), "32.9"));
}

TEST(SdfAnnotateOperands, DISABLED_AnEighthOperandIsReported) {
  ExpectReportedOnTheCall(
      CallerOf("",
               "$sdf_annotate(\"t.sdf\", top.a, \"c.cfg\", \"r.log\", "
               "\"MAXIMUM\", \"1.0:1.0:1.0\", \"FROM_MTM\", \"extra\");"),
      "$sdf_annotate takes at most seven operands");
}

TEST(SdfAnnotateOperands, SevenOperandsAreAccepted) {
  EXPECT_TRUE(
      ElabOk(CallerOf("",
                      "$sdf_annotate(\"t.sdf\", top.a, \"c.cfg\", \"r.log\", "
                      "\"MAXIMUM\", \"1.0:1.0:1.0\", \"FROM_MTM\");")));
}

TEST(SdfAnnotateOperands, DISABLED_ACallInsideAnExpressionIsReported) {
  ExpectReportedOnTheCall(
      CallerOf("  int x;\n", "x = $sdf_annotate(\"t.sdf\");"),
      "$sdf_annotate is a system task and cannot be called as a function");
}

TEST(SdfAnnotateOperands, ACallAsAStatementIsAccepted) {
  EXPECT_TRUE(ElabOk(CallerOf("  int x;\n", "$sdf_annotate(\"t.sdf\");")));
}

TEST(SdfAnnotateOperands, DISABLED_ARealSdfFileOperandIsReported) {
  ExpectReportedOnTheCall(
      CallerOf("  real fname = 1.5;\n", "$sdf_annotate(fname);"),
      "sdf_file operand of $sdf_annotate is not a string or integral value");
}

TEST(SdfAnnotateOperands, StringAndIntegralSdfFileOperandsAreAccepted) {
  EXPECT_TRUE(
      ElabOk(CallerOf("  string sname = \"t.sdf\";\n"
                      "  reg [8*5:1] rname = \"t.sdf\";\n",
                      "begin $sdf_annotate(sname); "
                      "$sdf_annotate(rname); end")));
}

TEST(SdfAnnotateOperands, DISABLED_AVariableAsTheModuleInstanceIsReported) {
  ExpectReportedOnTheCall(
      CallerOf("  reg r;\n", "$sdf_annotate(\"t.sdf\", r);"),
      "module_instance operand of $sdf_annotate names no instance");
}

TEST(SdfAnnotateOperands, DISABLED_AQuotedModuleInstanceIsReported) {
  ExpectReportedOnTheCall(CallerOf("", "$sdf_annotate(\"t.sdf\", \"top.a\");"),
                          "module_instance operand of $sdf_annotate names no "
                          "instance");
}

TEST(SdfAnnotateOperands, AnUnquotedInstanceNameIsAccepted) {
  EXPECT_TRUE(ElabOk(CallerOf("", "$sdf_annotate(\"t.sdf\", top.a);")));
}

}  // namespace
