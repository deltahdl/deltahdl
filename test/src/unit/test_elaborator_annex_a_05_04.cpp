#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

void ExpectReportedBeforeTheUdp(const std::string& instance,
                                const char* message, const char* subclause) {
  ElabFixture f;
  ElaborateSrc("module m;\n  logic y, a, b;\n  " + instance +
                   "\nendmodule\n"
                   "primitive p(output y, input a, input b);\n"
                   "  table\n"
                   "    0 0 : 0;\n"
                   "    1 ? : 1;\n"
                   "  endtable\n"
                   "endprimitive\n",
               f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, subclause))
      << instance;
}

TEST(UdpInstanceTerminalElaboration, TooFewTerminalsToALaterUdpAreReported) {
  ExpectReportedBeforeTheUdp(
      "p u(y);",
      "primitive 'p' takes 3 terminal(s) but this instance connects 1", "29.8");
  ExpectReportedBeforeTheUdp(
      "p u();",
      "primitive 'p' takes 3 terminal(s) but this instance connects 0", "29.8");
}

TEST(UdpInstanceTerminalElaboration, AnEmptyOrAttributedInputIsReported) {
  ExpectReportedBeforeTheUdp(
      "p u(y, , b);", "a UDP instance's input terminal is left empty", "A.5.4");
  ExpectReportedBeforeTheUdp("p u(y, (* k *) a, b);",
                             "a UDP instance's terminal takes no attribute "
                             "instance",
                             "A.5.4");
}

TEST(UdpInstanceTerminalElaboration, EveryTerminalConnectedIsFine) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("primitive p(output y, input a, input b);\n"
             "  table\n"
             "    0 0 : 0;\n"
             "    1 ? : 1;\n"
             "  endtable\n"
             "endprimitive\n"
             "module m;\n  logic y, a, b;\n  p u(y, a, b);\nendmodule\n",
             f));
}

}  // namespace
