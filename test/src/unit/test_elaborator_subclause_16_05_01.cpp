#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kMessage[] =
    "a clocking block input read as a sampled value shall be sampled with a "
    "#1step input skew";

const char kAssertRead[] = "assert property (@(posedge clk) cb.a);";

std::string InTop(const std::string& block, const std::string& items,
                  const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  parameter P = 2;\n"
         "  logic clk = 0, a = 0, x;\n"
         "  clocking cb @(posedge clk);\n"
         "    " +
         block +
         "\n"
         "  endclocking\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

std::string WithSkew(std::string src, const std::string& skew) {
  for (size_t at = src.find("SKEW"); at != std::string::npos;
       at = src.find("SKEW", at)) {
    src.replace(at, 4, skew);
  }
  return src;
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  auto* design = Elaborate(src, f);
  ASSERT_NE(design, nullptr) << src;
  EXPECT_FALSE(f.has_errors) << src;
}

void ExpectReported(const std::string& src, std::string_view read) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage,
                            LineHolding(src, read), "16.5.1"))
      << src;
}

void ExpectReportedBesideOneStep(const std::string& src,
                                 std::string_view read) {
  ExpectReported(WithSkew(src, "#2"), read);
  ExpectAccepted(WithSkew(src, "#1step"));
}

void ExpectEachBlockReported(std::initializer_list<const char*> blocks) {
  for (const char* block : blocks) {
    ExpectReported(InTop(block, kAssertRead), kAssertRead);
  }
}

void ExpectEachBlockAccepted(std::initializer_list<const char*> blocks) {
  for (const char* block : blocks) ExpectAccepted(InTop(block, kAssertRead));
}

TEST(ClockvarSamplingReport, EveryOneStepSkewReadByAnAssertionIsAccepted) {
  ExpectEachBlockAccepted(
      {"input a;", "input #1step a;", "default input #1step; input a;",
       "default input #2; input #1step a;", "inout a;",
       "default input #1step; inout a;", "input #1step output #1 a;"});
}

TEST(ClockvarSamplingReport, DISABLED_ANumericSkewReadByAnAssertionIsReported) {
  ExpectEachBlockReported({"input #2 a;"});
  ExpectEachBlockAccepted({"input #1step a;"});
}

TEST(ClockvarSamplingReport,
     DISABLED_AZeroTimeLiteralOrParameterSkewIsReported) {
  ExpectEachBlockReported({"input #0 a;", "input #2ns a;", "input #P a;"});
}

TEST(ClockvarSamplingReport, DISABLED_ADefaultSkewOtherThanOneStepIsReported) {
  ExpectEachBlockReported({"default input #1; input a;"});
  ExpectEachBlockAccepted({"default input #1step; input a;"});
}

TEST(ClockvarSamplingReport, DISABLED_AnEdgeSkewIsReported) {
  ExpectEachBlockReported({"input negedge a;", "input posedge a;",
                           "input edge a;", "input posedge #1 a;"});
}

TEST(ClockvarSamplingReport, DISABLED_AnInoutsSkewOtherThanOneStepIsReported) {
  ExpectEachBlockReported(
      {"default input #2; inout a;", "input #2 output #1 a;"});
  ExpectEachBlockAccepted({"default input #1step; inout a;", "inout a;",
                           "input #1step output #1 a;"});
}

const char* const kReads[] = {
    "assume property (@(posedge clk) cb.a);",
    "cover property (@(posedge clk) cb.a);",
    "cover sequence (@(posedge clk) cb.a);",
    "always @(posedge clk) assert property (cb.a);",
    "initial expect (@(posedge clk) cb.a);",
    "assert property (@(posedge clk) $past(cb.a));",
    "assert property (@(posedge clk) $rose(cb.a));",
};

TEST(ClockvarSamplingReport, EveryReaderOfAOneStepClockvarIsAccepted) {
  for (const char* read : kReads) {
    ExpectAccepted(InTop("input #1step a;", read));
  }
}

TEST(ClockvarSamplingReport, DISABLED_EveryReaderOfAClockvarIsReported) {
  for (const char* read : kReads) {
    ExpectReported(InTop("input #2 a;", read), read);
  }
}

TEST(ClockvarSamplingReport,
     DISABLED_APropertyOrSequenceOfTheBlockAssertedIsReported) {
  ExpectReportedBesideOneStep(
      InTop("input SKEW a;\n    property p1; a; endproperty",
            "assert property (cb.p1);"),
      "property p1;");
  ExpectReportedBesideOneStep(
      InTop("input SKEW a;\n    sequence s1; a; endsequence",
            "assert property (cb.s1);"),
      "sequence s1;");
}

TEST(ClockvarSamplingReport, DISABLED_AModulesPropertyInstantiatedIsReported) {
  ExpectReportedBesideOneStep(
      InTop("input SKEW a;",
            "property pm; @(posedge clk) cb.a; endproperty\n"
            "  assert property (pm);"),
      "property pm;");
}

TEST(ClockvarSamplingReport, AProceduralReadOfAnySkewIsAccepted) {
  for (const char* block : {"input #2 a;", "input negedge a;"}) {
    ExpectAccepted(InTop(block, "always @(posedge clk) x = cb.a;"));
  }
}

TEST(ClockvarSamplingReport, AnUnreadOrUninstantiatedClockvarIsAccepted) {
  ExpectAccepted(InTop("input #2 a;", "assert property (@(posedge clk) a);"));
  ExpectAccepted(InTop("input #2 a;\n    property p1; a; endproperty",
                       "assert property (@(posedge clk) a);"));
}

TEST(ClockvarSamplingReport,
     DISABLED_AProceduralSampledValueFunctionIsReported) {
  for (const char* read : {"always @(posedge clk) if ($rose(cb.a)) x = 1;",
                           "always @(posedge clk) x = $sampled(cb.a);"}) {
    ExpectReported(InTop("input #2 a;", read), read);
  }
}

const char kChecker[] =
    "checker chk(logic v, logic c);\n"
    "  assert property (@(posedge c) v);\n"
    "endchecker\n";

TEST(ClockvarSamplingReport, DISABLED_ACheckerActualOrAlwaysFfReadIsReported) {
  ExpectReportedBesideOneStep(
      InTop("input SKEW a;", "chk k(cb.a, clk);", kChecker), "chk k(cb.a");
  ExpectReportedBesideOneStep(InTop("input SKEW a;",
                                    "checker ck2;\n"
                                    "    logic q;\n"
                                    "    always_ff @(posedge clk) q <= cb.a;\n"
                                    "  endchecker\n"
                                    "  ck2 k2();"),
                              "q <= cb.a");
}

TEST(ClockvarSamplingReport, ACheckerReadingTheSignalByItsNameIsAccepted) {
  ExpectAccepted(InTop("input #2 a;", "chk k(a, clk);", kChecker));
}

const char kInterface[] =
    "interface ifc(input logic clk);\n"
    "  logic a = 0;\n"
    "  clocking cb @(posedge clk);\n"
    "    input SKEW a;\n"
    "  endclocking\n"
    "  modport mp(clocking cb);\n"
    "  assert property (@(posedge clk) cb.a);\n"
    "endinterface\n"
    "module mm(ifc.mp p, input logic clk);\n"
    "  assert property (@(posedge clk) p.cb.a);\n"
    "endmodule\n";

TEST(ClockvarSamplingReport, DISABLED_AnInterfacesClockvarIsReported) {
  const std::string kItems =
      "ifc i(clk);\n  mm u(i, clk);\n"
      "  assert property (@(posedge clk) i.cb.a);";
  for (const char* read :
       {"  assert property (@(posedge clk) cb.a);", "p.cb.a", "i.cb.a"}) {
    ExpectReportedBesideOneStep(InTop("input a;", kItems, kInterface), read);
  }
}

TEST(ClockvarSamplingReport,
     DISABLED_AProgramCheckerOrGenerateBlocksClockvarIsReported) {
  const char kRead[] = "assert property (@(posedge clk) cb2.a);";
  const std::string kUnit =
      "  logic a2 = 0;\n"
      "  clocking cb2 @(posedge clk); input SKEW a2; endclocking\n"
      "  assert property (@(posedge clk) cb2.a2);\n";
  ExpectReportedBesideOneStep(
      InTop("input a;", "pg p(clk);",
            "program pg(input logic clk);\n" + kUnit + "endprogram\n"),
      "cb2.a2");
  ExpectReportedBesideOneStep(
      InTop("input a;", "cc k(clk);",
            "checker cc(logic clk);\n" + kUnit + "endchecker\n"),
      "cb2.a2");
  ExpectReportedBesideOneStep(
      InTop("input a;",
            "if (1) begin : g\n"
            "    clocking cb2 @(posedge clk); input SKEW a; endclocking\n"
            "    " +
                std::string(kRead) + "\n  end"),
      kRead);
}

}  // namespace
