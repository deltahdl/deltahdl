#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerVariables, RandQualifierMarksCheckerVariable) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool saw_rand = false;
  for (const auto* item : r.cu->checkers[0]->items) {
    if (item->is_rand) saw_rand = true;
  }
  EXPECT_TRUE(saw_rand);
}

TEST(CheckerVariables, PlainCheckerVariableIsNotRand) {
  auto r = Parse(
      "checker chk;\n"
      "  bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  for (const auto* item : r.cu->checkers[0]->items) {
    EXPECT_FALSE(item->is_rand);
  }
}

TEST(CheckerVariables, ConstFreeVariableParses) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  rand const bit [5:0] idx;\n"
              "endchecker\n"));
}

TEST(CheckerVariables, AutomaticCheckerVariableIsIllegal) {
  auto r = Parse(
      "checker chk;\n"
      "  automatic bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "'automatic' is not allowed in a data_declaration "
                            "outside a procedural context",
                            2, "6.8"));
}

}  // namespace
