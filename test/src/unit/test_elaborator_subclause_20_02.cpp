#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SimulationControlArguments, DISABLED_AnArgumentBeyondTheSyntaxIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial $exit(1);\n"
      "  initial $finish(1, 2);\n"
      "  initial $stop(0, 1);\n"
      "endmodule\n",
      f);
  for (auto [line, message] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {2u, "$exit takes no argument"},
           {3u, "$finish takes at most one argument"},
           {4u, "$stop takes at most one argument"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "20.2"))
        << message;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(SimulationControlArguments, TheArgumentsTheSyntaxGivesAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  localparam int kLevel = 1;\n"
      "  initial $exit;\n"
      "  initial $exit();\n"
      "  initial $finish;\n"
      "  initial $finish(2);\n"
      "  initial $finish(kLevel);\n"
      "  initial $stop;\n"
      "  initial $stop(0);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(SimulationControlArguments, DISABLED_ALevelOutsideZeroToTwoIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial $finish(3);\n"
      "  initial $stop(-1);\n"
      "  initial $finish(\"a\");\n"
      "  initial $finish(1'bx);\n"
      "endmodule\n",
      f);
  for (const auto& [line, task] :
       std::initializer_list<std::pair<uint32_t, std::string>>{
           {2u, "$finish"}, {3u, "$stop"}, {4u, "$finish"}, {5u, "$finish"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the argument of " + task + " is 0, 1 or 2", line,
                              "20.2"))
        << task << " at line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

}  // namespace
