#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string WithClassVariables(std::string_view use) {
  return std::string(
             "class C;\nendclass\nclass D;\nendclass\nmodule t;\n"
             "  C c, e;\n  D d;\n  int i;\n  initial ")
      .append(use)
      .append("\nendmodule\n");
}

::testing::AssertionResult ReportedOn(std::string_view use,
                                      std::string_view message) {
  ElabFixture f;
  std::string src = WithClassVariables(use);
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, LineHolding(src, use),
                       "8.4");
}

TEST(ClassDataType, AClassVariableHoldingAnIntegralValueIsReported) {
  EXPECT_TRUE(ReportedOn("c = 5;", "cannot assign non-class value"));
}

TEST(ClassDataType, AClassVariableReadIntoAnIntegralVariableIsReported) {
  EXPECT_TRUE(ReportedOn("i = c;", "cannot assign class object handle"));
}

TEST(ClassDataType, AClassVariableHoldingAnUnrelatedClassHandleIsReported) {
  EXPECT_TRUE(ReportedOn("c = d;", "assignment compatible types"));
}

TEST(ClassDataType, AClassVariableHoldingANewObjectAHandleOrNullIsAccepted) {
  EXPECT_TRUE(ElabOk(WithClassVariables(
      "begin\n    c = new;\n    e = c;\n    c = null;\n    d = new;\n"
      "  end")));
}

}  // namespace
