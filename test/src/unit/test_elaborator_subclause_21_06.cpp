#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string PlusargsIn(const std::string& call) {
  return "module t;\n"
         "  int v, u; real r; wire [7:0] w; string s;\n"
         "  initial v = " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call, const char* message) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(PlusargsIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "21.6")) << call;
}

void ExpectAccepted(const std::string& call) {
  ElabFixture f;
  Elaborate(PlusargsIn(call), f);
  EXPECT_FALSE(f.has_errors) << call;
}

constexpr const char* kTestShape = "$test$plusargs takes one search string";
constexpr const char* kValueShape =
    "$value$plusargs takes a user string and a variable";
constexpr const char* kValueDestination =
    "the second argument of $value$plusargs must be a variable";
constexpr const char* kTestOperand =
    "the search string of $test$plusargs must be a string or an integral "
    "value";
constexpr const char* kValueOperand =
    "the user string of $value$plusargs must be a string or an integral value";
constexpr const char* kOneFormat =
    "the user string of $value$plusargs must name exactly one format";

TEST(TestPlusargsArgumentList, DISABLED_NoArgumentIsReported) {
  ExpectReported("$test$plusargs()", kTestShape);
}

TEST(TestPlusargsArgumentList, DISABLED_TwoArgumentsAreReported) {
  ExpectReported("$test$plusargs(\"A\", \"B\")", kTestShape);
}

TEST(TestPlusargsArgumentList, DISABLED_ARealSearchStringIsReported) {
  ExpectReported("$test$plusargs(r)", kTestOperand);
}

TEST(TestPlusargsArgumentList, StringAndIntegralSearchStringsAreAccepted) {
  for (const char* call :
       {"$test$plusargs(\"A\")", "$test$plusargs(s)", "$test$plusargs(u)"}) {
    ExpectAccepted(call);
  }
}

TEST(ValuePlusargsArgumentList, DISABLED_OneArgumentIsReported) {
  ExpectReported("$value$plusargs(\"N=%d\")", kValueShape);
}

TEST(ValuePlusargsArgumentList, DISABLED_ThreeArgumentsAreReported) {
  ExpectReported("$value$plusargs(\"N=%d\", u, u)", kValueShape);
}

TEST(ValuePlusargsArgumentList, DISABLED_ALiteralDestinationIsReported) {
  ExpectReported("$value$plusargs(\"N=%d\", 5)", kValueDestination);
}

TEST(ValuePlusargsArgumentList, DISABLED_ANetDestinationIsReported) {
  ExpectReported("$value$plusargs(\"N=%d\", w)", kValueDestination);
}

TEST(ValuePlusargsArgumentList, DISABLED_ARealUserStringIsReported) {
  ExpectReported("$value$plusargs(r, u)", kValueOperand);
}

TEST(ValuePlusargsArgumentList, DISABLED_AUserStringWithNoFormatIsReported) {
  ExpectReported("$value$plusargs(\"A\", u)", kOneFormat);
}

TEST(ValuePlusargsArgumentList, DISABLED_AUserStringWithTwoFormatsIsReported) {
  ExpectReported("$value$plusargs(\"A=%d%d\", u)", kOneFormat);
}

TEST(ValuePlusargsArgumentList, EveryAllowedFormIsAccepted) {
  for (const char* call :
       {"$value$plusargs(\"N=%d\", u)", "$value$plusargs(s, u)",
        "$value$plusargs(u, s)", "$value$plusargs(\"R=%f\", r)",
        "$value$plusargs(\"N=%0D\", u)"}) {
    ExpectAccepted(call);
  }
}

}  // namespace
