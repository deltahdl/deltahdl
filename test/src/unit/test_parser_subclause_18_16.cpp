#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InInitial(const std::string& body) {
  return "module t;\n"
         "  int x;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(RandcaseForms, AnItemWithItsColonIsAccepted) {
  EXPECT_TRUE(
      ParseOk(InInitial("    randcase\n"
                        "      1 : x = 1;\n"
                        "    endcase\n")));
}

TEST(RandcaseForms, AnItemWithoutAColonIsRejected) {
  auto r =
      Parse(InInitial("    randcase\n"
                      "      1 x = 1;\n"
                      "    endcase\n"));
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ':', got identifier", 5, "18.16"));
}

TEST(RandcaseForms, ItemsWithoutEndcaseAreRejected) {
  auto r =
      Parse(InInitial("    randcase\n"
                      "      1 : x = 1;\n"
                      "      2 : x = 2;\n"));
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endcase'", 9, "18.16"));
}

}  // namespace
