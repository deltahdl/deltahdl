#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ClassDeclaration, MalformedClassItemNames8_3) {
  // §8.3, Syntax 8-1 footnote 10: "In any one declaration, only one of
  // protected or local is allowed, only one of rand or randc is allowed, and
  // static and/or virtual can appear only once." The report names §8.3, which
  // is what tells this rejection from every other way a class body is
  // rejected: a member whose type will not parse, a stray token, an end label
  // that does not match. All of them leave has_errors true.
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  const auto* diag =
      FindDiag(r, "cannot combine 'local' and 'protected' qualifiers");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "8.3");
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

}  // namespace
