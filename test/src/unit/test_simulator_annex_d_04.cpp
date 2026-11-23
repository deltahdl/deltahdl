#include <gtest/gtest.h>

#include <string>

#include "helpers_annex_d_call_forms.h"

namespace {

constexpr const char* kOneFilenameTask =
    "$input is written as a task statement whose one argument is a string "
    "naming the command file, and this call is not";

void ExpectReportedBesideAWellFormedInput(const std::string& malformed) {
  ExpectOnlyTheMalformedCallReported("$input(\"cmds.txt\")", malformed,
                                     kOneFilenameTask, "D.4");
}

TEST(InputTaskForm, DISABLED_ACallWithNoFilenameIsReported) {
  ExpectReportedBesideAWellFormedInput("$input");
}

TEST(InputTaskForm, DISABLED_ACallWithTwoArgumentsIsReported) {
  ExpectReportedBesideAWellFormedInput("$input(\"x.txt\", \"y.txt\")");
}

TEST(InputTaskForm, DISABLED_ACallWhoseArgumentIsNoStringIsReported) {
  ExpectReportedBesideAWellFormedInput("$input(42)");
}

TEST(InputTaskForm, DISABLED_ACallUsedAsAFunctionIsReported) {
  ExpectReportedBesideAWellFormedInput("v = $input(\"a.txt\")");
}

}  // namespace
