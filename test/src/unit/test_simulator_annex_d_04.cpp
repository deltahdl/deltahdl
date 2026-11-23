#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kOneFilenameTask =
    "$input is written as a task statement whose one argument is a string "
    "naming the command file, and this call is not";

std::string InputCallsBesideAWellFormedOne(const std::string& stmt) {
  std::string src =
      "module t;\n"
      "  int v;\n"
      "  initial begin\n"
      "    $input(\"cmds.txt\");\n"
      "    ";
  src += stmt;
  src +=
      ";\n"
      "  end\n"
      "endmodule\n";
  return src;
}

void ExpectOnlyTheMalformedCallReported(const std::string& stmt) {
  const std::string kSrc = InputCallsBesideAWellFormedOne(stmt);
  SimFixture f;
  auto* design = ElaborateSrc(kSrc, f);
  if (design != nullptr) LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneFilenameTask,
                            LineHolding(kSrc, stmt + ";"), "D.4"))
      << kSrc;
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kOneFilenameTask,
                             LineHolding(kSrc, "$input(\"cmds.txt\")"), "D.4"))
      << kSrc;
}

TEST(InputTaskForm, DISABLED_ACallWithNoFilenameIsReported) {
  ExpectOnlyTheMalformedCallReported("$input");
}

TEST(InputTaskForm, DISABLED_ACallWithTwoArgumentsIsReported) {
  ExpectOnlyTheMalformedCallReported("$input(\"x.txt\", \"y.txt\")");
}

TEST(InputTaskForm, DISABLED_ACallWhoseArgumentIsNoStringIsReported) {
  ExpectOnlyTheMalformedCallReported("$input(42)");
}

TEST(InputTaskForm, DISABLED_ACallUsedAsAFunctionIsReported) {
  ExpectOnlyTheMalformedCallReported("v = $input(\"a.txt\")");
}

}  // namespace
