#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SourceText, ClassPropertyWithQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  randc bit [3:0] y;\n"
      "  static int count;\n"
      "  protected int secret;\n"
      "  local int hidden;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand);
  EXPECT_EQ(members[0]->name, "x");
  EXPECT_TRUE(members[1]->is_randc);
  EXPECT_EQ(members[1]->name, "y");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_local);
}

TEST(ClassSyntaxParsing, ErrorBothRandAndRandc) {
  auto r = Parse(
      "class C;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'rand' and 'randc' qualifiers", 2, "8.3"));
}

TEST(ClassSyntaxParsing, ErrorRandcBeforeRand) {
  auto r = Parse(
      "class C;\n"
      "  randc rand bit [1:0] x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'rand' and 'randc' qualifiers", 2, "8.3"));
}

TEST(ClassSyntaxParsing, ARandomQualifierMixesWithClassItemQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  static rand int a;\n"
      "  rand static int b;\n"
      "  local randc bit [1:0] c;\n"
      "  randc protected bit [1:0] d;\n"
      "  static local rand int e;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand && members[0]->is_static);
  EXPECT_TRUE(members[1]->is_rand && members[1]->is_static);
  EXPECT_TRUE(members[2]->is_randc && members[2]->is_local);
  EXPECT_TRUE(members[3]->is_randc && members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_rand && members[4]->is_static &&
              members[4]->is_local);
}

}  // namespace
