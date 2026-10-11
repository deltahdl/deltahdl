#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(ClassDeclaration, MalformedClassItemNames8_3) {
  // §8.3, Syntax 8-1 footnote 10: a single declaration takes at most one of
  // protected and local, at most one of rand and randc, and static and virtual
  // once each at most. The report names §8.3, which is what tells this
  // rejection from every other way a class body is rejected: a member whose
  // type will not parse, a stray token, an end label that does not match. All
  // of them leave has_errors true.
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'local' and 'protected' qualifiers", 2, "8.3"));
}

TEST(ClassDeclaration, ClassItemWithOneAccessQualifierIsAccepted) {
  // The counterpart that keeps the case above about the combination rather
  // than about the qualifier: one access qualifier on a class_property is
  // legal, so a parser that rejected `local` outright would fail here.
  auto r = Parse(
      "class C;\n"
      "  local int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Syntax 8-1 gives class_declaration no lifetime: `class` is followed by an
// optional final_specifier and the class name. Each lifetime keyword written
// there is reported at the keyword, and the class it stands in is still read,
// so the name after it declares the class.
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
