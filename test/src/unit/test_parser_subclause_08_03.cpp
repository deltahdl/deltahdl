#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(ClassDeclaration, MalformedClassItemNames8_3) {
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'local' and 'protected' qualifiers", 2, "8.3"));
}

TEST(ClassDeclaration, ClassItemWithOneAccessQualifierIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  local int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassDeclaration, ALifetimeAfterClassIsReported) {
  auto r = Parse(
      "class automatic A; endclass\n"
      "class static B; endclass\n"
      "module m; A a; B b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a class declaration takes no lifetime; "
                            "'automatic' stands where its name belongs",
                            1, "8.3"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a class declaration takes no lifetime; "
                            "'static' stands where its name belongs",
                            2, "8.3"));
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "A");
  EXPECT_EQ(r.cu->classes[1]->name, "B");
}

}  // namespace
