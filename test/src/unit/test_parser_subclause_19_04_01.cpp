#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(EmbeddedCovergroupInheritance, ExtendsFormParses) {
  auto r = Parse(
      "class base;\n"
      "  enum {red, green, blue} color;\n"
      "  covergroup g1;\n"
      "    c: coverpoint color;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit d;\n"
      "  covergroup extends g1;\n"
      "    coverpoint d;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);

  const ClassMember* derived_cg = nullptr;
  for (auto* m : r.cu->classes[1]->members) {
    if (m->kind == ClassMemberKind::kCovergroup) derived_cg = m;
  }
  ASSERT_NE(derived_cg, nullptr);
  EXPECT_EQ(derived_cg->name, "g1");
  EXPECT_EQ(derived_cg->covergroup_extends_base, "g1");
}

TEST(EmbeddedCovergroupInheritance, ExtendsFormWithEndLabelParses) {
  auto r = Parse(
      "class base;\n"
      "  bit a;\n"
      "  covergroup g1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit d;\n"
      "  covergroup extends g1;\n"
      "    coverpoint d;\n"
      "  endgroup :g1\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(EmbeddedCovergroupInheritance, PlainCovergroupHasNoExtendsBase) {
  auto r = Parse(
      "class C;\n"
      "  bit x;\n"
      "  covergroup g1;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassMember* cg = nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kCovergroup) cg = m;
  }
  ASSERT_NE(cg, nullptr);
  EXPECT_EQ(cg->name, "g1");
  EXPECT_TRUE(cg->covergroup_extends_base.empty());
}

TEST(EmbeddedCovergroupInheritance, ExtendsFormEmptyBodyParses) {
  auto r = Parse(
      "class base;\n"
      "  bit a;\n"
      "  covergroup g1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g1;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);

  const ClassMember* derived_cg = nullptr;
  for (auto* m : r.cu->classes[1]->members) {
    if (m->kind == ClassMemberKind::kCovergroup) derived_cg = m;
  }
  ASSERT_NE(derived_cg, nullptr);
  EXPECT_EQ(derived_cg->name, "g1");
  EXPECT_EQ(derived_cg->covergroup_extends_base, "g1");
}

TEST(EmbeddedCovergroupInheritance, ExtendsFormRequiresBaseIdentifier) {
  auto r = Parse(
      "class base;\n"
      "  bit a;\n"
      "  covergroup g1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit d;\n"
      "  covergroup extends ;\n"
      "    coverpoint d;\n"
      "  endgroup\n"
      "endclass\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 9, "19.4.1"));
}

}  // namespace
