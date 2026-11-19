#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckNotifierElaboration, LocalNetNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  wire n;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 'n' is a net, not a "
                            "variable",
                            4, "31.6"));
}

TEST(TimingCheckNotifierElaboration, NetPortNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk, output wire n);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 2, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 'n' is a net, not a "
                            "variable",
                            3, "31.6"));
}

TEST(TimingCheckNotifierElaboration, VariableNotifiersAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk, output reg pr);\n"
      "  reg r; integer i; logic l;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, r);\n"
      "    $setup(d, posedge clk, 5, i);\n"
      "    $setup(d, posedge clk, 5, l);\n"
      "    $setup(d, posedge clk, 5, pr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

void ExpectNotifierRejected(const std::string& before, const char* notifier,
                            const std::string& msg, int line,
                            const char* subclause) {
  ElabFixture f;
  std::string src = before +
                    "module m(input d, clk);\n"
                    "  specify\n"
                    "    $setup(d, posedge clk, 5, " +
                    notifier +
                    ");\n"
                    "  endspecify\n"
                    "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, line, subclause)) << src;
}

TEST(TimingCheckNotifierElaboration, InputPortNotifierRejected) {
  ExpectNotifierRejected(
      "", "d", "timing check notifier 'd' is a net, not a variable", 3, "31.6");
}

TEST(TimingCheckNotifierElaboration, OutputRegPortNotifierAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk, output reg n);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckNotifierElaboration, TriAndUwireNotifiersRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  tri t;\n"
      "  uwire u;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, t);\n"
      "    $setup(d, posedge clk, 5, u);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 't' is a net, not a "
                            "variable",
                            5, "31.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 'u' is a net, not a "
                            "variable",
                            6, "31.6"));
}

TEST(TimingCheckNotifierElaboration,
     VariableDeclaredAfterTheSpecifyBlockAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, late);\n"
      "  endspecify\n"
      "  reg late;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckNotifierElaboration, DISABLED_UndeclaredNotifierRejected) {
  ExpectNotifierRejected(
      "", "nope",
      "timing check notifier 'nope' is not a variable declared in the module",
      3, "31.6");
}

TEST(TimingCheckNotifierElaboration, DISABLED_ParameterNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  parameter P = 0;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, P);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "timing check notifier 'P' is not a variable declared in the module", 4,
      "31.6"));
}

TEST(TimingCheckNotifierElaboration,
     DISABLED_CompilationUnitVariableNotifierRejected) {
  ExpectNotifierRejected(
      "logic un;\n", "un",
      "timing check notifier 'un' is not a variable declared in the module", 4,
      "31.6");
}

TEST(TimingCheckNotifierElaboration,
     DISABLED_ImportedPackageVariableNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  logic pn;\n"
      "endpackage\n"
      "module m(input d, clk);\n"
      "  import pk::*;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, pn);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "timing check notifier 'pn' is not a variable declared in the module", 7,
      "31.6"));
}

}  // namespace
