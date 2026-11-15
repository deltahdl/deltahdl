#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CovergroupInCheckerPlacement, CovergroupInCheckerBodyParses) {
  EXPECT_TRUE(
      ParseOk("checker chk(logic clk, logic active);\n"
              "  covergroup cg_active @(posedge clk);\n"
              "    cp_active : coverpoint active;\n"
              "  endgroup\n"
              "endchecker\n"));
}

TEST(CovergroupInCheckerPlacement, CovergroupInsideProceduralBlockIsRejected) {
  auto r = Parse(
      "checker chk(logic clk, logic active);\n"
      "  always_ff @(posedge clk) begin\n"
      "    covergroup cg_active @(posedge clk);\n"
      "      cp_active : coverpoint active;\n"
      "    endgroup\n"
      "  end\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(CovergroupInCheckerPlacement, ADeclarationInEachProcedureIsRejected) {
  for (const char* proc : {"initial", "always_comb", "always_latch", "final"}) {
    std::string src = "checker chk(logic clk, logic active);\n  ";
    src += proc;
    src +=
        " begin\n"
        "    covergroup cg_active @(posedge clk);\n"
        "      cp_active : coverpoint active;\n"
        "    endgroup\n"
        "  end\n"
        "endchecker\n";
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"))
        << proc;
  }
}

}  // namespace
