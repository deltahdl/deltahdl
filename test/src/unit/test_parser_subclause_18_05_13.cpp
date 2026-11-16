#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_constraint_item_places.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

TEST(SoftConstraintParsing, SoftRelationCapturedAsSoftNotHard) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { soft x == 42; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
  EXPECT_TRUE(m->constraint_exprs.empty());
}

TEST(SoftConstraintParsing, HardAndSoftInSameBlockSeparated) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; soft x == 5; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_exprs.size(), 1u);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
}

TEST(SoftConstraintParsing, DisableSoftOnAnArraysSizeIsRecorded) {
  auto r = Parse(
      "class D;\n"
      "  rand int v;\n"
      "endclass\n"
      "class C;\n"
      "  rand int a[];\n"
      "  rand int b[$];\n"
      "  rand D h;\n"
      "  constraint c { disable soft a.size(); disable soft b.size;\n"
      "                 disable soft h.v; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.back(), "c");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->constraint_disable_soft_refs.size(), 2u);
  EXPECT_EQ(m->constraint_disable_soft_refs[0].name, "a.size");
  EXPECT_EQ(m->constraint_disable_soft_refs[1].name, "b.size");
}

const char* const kSoftDecl = "bit [3:0] x, z; bit mode; int length; int a[4];";
const char* const kItemsDoNotParse =
    "the constraint block's items do not parse from here";

void ExpectSoftRejected(ItemPlace place, const std::string& item) {
  auto r = Parse(ItemIn(place, kSoftDecl, item));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 5, "A.1.10"))
      << ItemPlaceName(place) << ": " << item;
}

void ExpectSoftAccepted(ItemPlace place, const std::string& item) {
  auto r = Parse(ItemIn(place, kSoftDecl, item));
  EXPECT_FALSE(r.has_errors) << ItemPlaceName(place) << ": " << item;
}

TEST(SoftConstraintParsing, SoftBeforeABraceIsRejectedEverywhere) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectSoftRejected(place, "soft { x == 3; }");
    ExpectSoftRejected(place, "soft mode -> { length == 1024; }");
  }
}

TEST(SoftConstraintParsing, SoftBeforeAnExpressionIsAcceptedEverywhere) {
  for (ItemPlace place : kEveryItemPlace) {
    for (const char* item :
         {"soft x == 3;", "soft mode -> length == 1024;",
          "soft x dist {1 := 1, [2:3] :/ 2};", "soft x inside {1, [4:6]};",
          "if (mode) soft x == 3;", "if (mode) z == 0; else soft x == 3;",
          "mode -> soft x == 3;", "foreach (a[i]) soft a[i] == i;"}) {
      ExpectSoftAccepted(place, item);
    }
  }
}

}  // namespace
