#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InInitial(const std::string& stmt) {
  return "module m;\n"
         "  int a, ok;\n"
         "  initial begin\n"
         "    " +
         stmt +
         "\n"
         "  end\n"
         "endmodule\n";
}

TEST(ScopeRandomizeForms, DISABLED_ALiteralArgumentToTheBareFormIsRejected) {
  ElabFixture f;
  ElabOk(InInitial("ok = randomize(5);"), f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to a scope randomize call shall be a variable identifier", 4,
      "A.8.2"));
}

TEST(ScopeRandomizeForms, AVariableArgumentToTheBareFormIsAccepted) {
  EXPECT_TRUE(ElabOk(InInitial("ok = randomize(a);")));
}

TEST(ScopeRandomizeForms, AWithListInTheStdFormIsRejected) {
  ElabFixture f;
  ElabOk(InInitial("ok = std::randomize(a) with (a) { a > 0; };"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope randomize call cannot use a parenthesized "
                            "identifier list after 'with'",
                            4, "A.8.2"));
}

TEST(ScopeRandomizeForms, TheStdFormWithABlockAloneIsAccepted) {
  EXPECT_TRUE(ElabOk(InInitial("ok = std::randomize(a) with { a > 0; };")));
}

}  // namespace
