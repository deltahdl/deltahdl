#include <gtest/gtest.h>

#include <string>

#include "helpers_annex_d_call_forms.h"

namespace {

constexpr const char* kSaveTasks[] = {"$save", "$restart", "$incsave"};

std::string WellFormedCall(const std::string& task) {
  std::string call = task;
  call += "(\"state.dat\")";
  return call;
}

std::string FormMessage(const std::string& task) {
  std::string message = task;
  message +=
      " is written as a task statement whose one argument is a file name in "
      "quotation marks, and this call is not";
  return message;
}

void ExpectEachTaskReported(const std::string& malformed_args) {
  for (const char* task : kSaveTasks) {
    std::string well_formed = WellFormedCall(task);
    std::string malformed = task;
    malformed += malformed_args;
    ExpectOnlyTheMalformedCallReported(well_formed, malformed,
                                       FormMessage(task), "D.9");
  }
}

TEST(SaveTaskForm, DISABLED_ACallWithNoArgumentIsReported) {
  ExpectEachTaskReported("");
}

TEST(SaveTaskForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectEachTaskReported("()");
}

TEST(SaveTaskForm, DISABLED_TwoArgumentsAreReported) {
  ExpectEachTaskReported("(\"a.dat\", \"b.dat\")");
}

TEST(SaveTaskForm, DISABLED_AnIntegerArgumentIsReported) {
  ExpectEachTaskReported("(3)");
}

TEST(SaveTaskForm, DISABLED_AStringExpressionArgumentIsReported) {
  for (const char* task : kSaveTasks) {
    std::string well_formed = WellFormedCall(task);
    std::string malformed = task;
    malformed += "($sformatf(\"%0d.dat\", v))";
    ExpectOnlyTheMalformedCallReported(well_formed, malformed,
                                       FormMessage(task), "D.9");
  }
}

TEST(SaveTaskForm, DISABLED_ACallUsedAsAFunctionIsReported) {
  for (const char* task : kSaveTasks) {
    std::string well_formed = WellFormedCall(task);
    ExpectOnlyTheMalformedCallReported(well_formed, "v = " + well_formed,
                                       FormMessage(task), "D.9");
  }
}

}  // namespace
