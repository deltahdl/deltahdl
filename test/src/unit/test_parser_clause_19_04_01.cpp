#include "fixture_parser.h"

using namespace delta;

namespace {

// §19.4.1: a derived embedded covergroup is written with the inheritance form
// `covergroup extends base ;`. There is no fresh name between `covergroup` and
// `extends`; the derived covergroup adopts the base covergroup_identifier as
// its own name. The form must parse, and the member must record both that name
// and the base it extends.
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
  // The derived covergroup reuses the base covergroup's name.
  EXPECT_EQ(derived_cg->name, "g1");
  EXPECT_EQ(derived_cg->covergroup_extends_base, "g1");
}

// §19.4.1: the endgroup of a derived covergroup may carry the optional trailing
// `: covergroup_identifier` label naming the (shared) covergroup. The label
// repeating the base name is accepted.
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

// §19.4.1: the inheritance form does not disturb the ordinary, non-derived
// covergroup declaration. A plain embedded covergroup still parses and carries
// no extended base.
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

// §19.4.1: the extends form names the base covergroup with a required
// covergroup_identifier. Omitting that identifier (`covergroup extends ;`) is a
// syntax error reported by the parser.
TEST(EmbeddedCovergroupInheritance, ExtendsFormRequiresBaseIdentifier) {
  EXPECT_FALSE(
      ParseOk("class base;\n"
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
              "endclass\n"));
}

}  // namespace
