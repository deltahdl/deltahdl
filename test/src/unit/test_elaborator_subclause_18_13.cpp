#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InInitial(const std::string& stmt) {
  return "class C;\n"
         "  rand bit [3:0] x;\n"
         "endclass\n"
         "module m;\n"
         "  C o = new;\n"
         "  mailbox mb = new;\n"
         "  int unsigned u;\n"
         "  int k;\n"
         "  string s;\n"
         "  initial begin\n"
         "    " +
         stmt +
         "\n"
         "  end\n"
         "endmodule\n";
}

void ExpectReport(const std::string& stmt, const std::string& msg,
                  const char* subclause) {
  ElabFixture f;
  ElabOk(InInitial(stmt), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 11, subclause)) << stmt;
}

void ExpectNoReportOnTheCall(const std::string& stmt) {
  ElabFixture f;
  ElabOk(InInitial(stmt), f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, uint32_t{11}) << stmt << ": " << d.message;
  }
}

TEST(RandomNumberCallForms, UrandomWithEmptyParenthesesOrOneSeedIsAccepted) {
  ExpectNoReportOnTheCall("u = $urandom();");
  ExpectNoReportOnTheCall("u = $urandom(5);");
}

TEST(RandomNumberCallForms, DISABLED_UrandomWithTwoArgumentsIsRejected) {
  ExpectReport("u = $urandom(1, 2);",
               "$urandom takes at most 1 argument; 2 given", "18.13.1");
}

TEST(RandomNumberCallForms, UrandomRangeWithOneOrTwoArgumentsIsAccepted) {
  ExpectNoReportOnTheCall("u = $urandom_range(7);");
  ExpectNoReportOnTheCall("u = $urandom_range(7, 1);");
}

TEST(RandomNumberCallForms, DISABLED_UrandomRangeWithNoArgumentsIsRejected) {
  ExpectReport("u = $urandom_range();",
               "$urandom_range takes at least 1 argument; 0 given", "18.13.2");
}

TEST(RandomNumberCallForms, DISABLED_UrandomRangeWithThreeArgumentsIsRejected) {
  ExpectReport("u = $urandom_range(1, 2, 3);",
               "$urandom_range takes at most 2 arguments; 3 given", "18.13.2");
}

TEST(RandomNumberCallForms, SrandomWithOneSeedIsAccepted) {
  ExpectNoReportOnTheCall("o.srandom(3);");
  ExpectNoReportOnTheCall("mb.srandom(3);");
}

TEST(RandomNumberCallForms, SrandomWithTwoSeedsOnAStdHandleIsRejected) {
  ExpectReport("mb.srandom(1, 2);",
               "method 'srandom' of class 'mailbox' takes at most 1 argument; "
               "2 given",
               "18.13.3");
}

TEST(RandomNumberCallForms, DISABLED_SrandomWithNoSeedOnAUserHandleIsRejected) {
  ExpectReport("o.srandom();",
               "method 'srandom' of class 'C' takes at least 1 argument; 0 "
               "given",
               "18.13.3");
}

TEST(RandomNumberCallForms,
     DISABLED_SrandomWithTwoSeedsOnAUserHandleIsRejected) {
  ExpectReport("o.srandom(1, 2);",
               "method 'srandom' of class 'C' takes at most 1 argument; 2 "
               "given",
               "18.13.3");
}

TEST(RandomNumberCallForms,
     DISABLED_SrandomUsedAsAValueOnAUserHandleIsRejected) {
  ExpectReport("k = o.srandom(1);",
               "srandom() is a void function and yields no value", "18.13.3");
}

TEST(RandomNumberCallForms,
     DISABLED_SrandomUsedAsAValueOnAStdHandleIsRejected) {
  ExpectReport("k = mb.srandom(1);",
               "srandom() is a void function and yields no value", "18.13.3");
}

TEST(RandomNumberCallForms, GetRandstateWithNoActualIsAccepted) {
  ExpectNoReportOnTheCall("s = o.get_randstate();");
  ExpectNoReportOnTheCall("s = mb.get_randstate();");
}

TEST(RandomNumberCallForms, GetRandstateWithAnActualOnAStdHandleIsRejected) {
  ExpectReport("s = mb.get_randstate(1);",
               "method 'get_randstate' of class 'mailbox' takes at most 0 "
               "arguments; 1 given",
               "18.13.4");
}

TEST(RandomNumberCallForms,
     DISABLED_GetRandstateWithAnActualOnAUserHandleIsRejected) {
  ExpectReport("s = o.get_randstate(1);",
               "method 'get_randstate' of class 'C' takes at most 0 "
               "arguments; 1 given",
               "18.13.4");
}

TEST(RandomNumberCallForms, SetRandstateWithOneStringIsAccepted) {
  ExpectNoReportOnTheCall("o.set_randstate(s);");
  ExpectNoReportOnTheCall("mb.set_randstate(s);");
}

TEST(RandomNumberCallForms, SetRandstateWithNoActualOnAStdHandleIsRejected) {
  ExpectReport("mb.set_randstate();",
               "method 'set_randstate' of class 'mailbox' takes at least 1 "
               "argument; 0 given",
               "18.13.5");
}

TEST(RandomNumberCallForms, SetRandstateWithTwoActualsOnAStdHandleIsRejected) {
  ExpectReport("mb.set_randstate(s, s);",
               "method 'set_randstate' of class 'mailbox' takes at most 1 "
               "argument; 2 given",
               "18.13.5");
}

TEST(RandomNumberCallForms,
     DISABLED_SetRandstateWithNoActualOnAUserHandleIsRejected) {
  ExpectReport("o.set_randstate();",
               "method 'set_randstate' of class 'C' takes at least 1 "
               "argument; 0 given",
               "18.13.5");
}

TEST(RandomNumberCallForms,
     DISABLED_SetRandstateWithTwoActualsOnAUserHandleIsRejected) {
  ExpectReport("o.set_randstate(s, s);",
               "method 'set_randstate' of class 'C' takes at most 1 "
               "argument; 2 given",
               "18.13.5");
}

TEST(RandomNumberCallForms, DISABLED_SetRandstateUsedAsAValueIsRejected) {
  ExpectReport("k = o.set_randstate(s);",
               "set_randstate() is a void function and yields no value",
               "18.13.5");
}

}  // namespace
