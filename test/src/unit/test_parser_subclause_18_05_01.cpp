#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

// Locate a constraint member of the given name within a parsed class.
const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

// 18.5.1: a constraint prototype may take an implicit form, written as a
// constraint declaration with a name but no block. The parser records such a
// member as a prototype that does not use the 'extern' keyword.
TEST(ExternalConstraintBlockParsing, ImplicitPrototypeFormRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint proto1;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "proto1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_prototype);
  EXPECT_FALSE(m->is_constraint_extern);
}

// 18.5.1: the explicit prototype form uses the 'extern' keyword before the
// named, bodyless constraint declaration. The parser marks it both as a
// prototype and as the extern form.
TEST(ExternalConstraintBlockParsing, ExplicitPrototypeFormRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "proto2");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_prototype);
  EXPECT_TRUE(m->is_constraint_extern);
}

// 18.5.1: a prototype is distinguished from an ordinary in-class constraint by
// the absence of a block. A constraint that carries a block is not a prototype.
TEST(ExternalConstraintBlockParsing, ConstraintWithBodyIsNotPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(m->is_constraint_prototype);
}

// 18.5.1: a prototype is completed by an external constraint block declared
// outside the class using the class scope resolution operator. The parser
// records the block's owning class and constraint name from 'C::proto2'.
TEST(ExternalConstraintBlockParsing, ExternalBlockRecordsClassAndName) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n"
      "constraint C::proto2 { x >= 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints.front().class_name, "C");
  EXPECT_EQ(r.cu->external_constraints.front().constraint_name, "proto2");
}

// 18.5.1 with 26.2: the block shares its scope with the class it completes,
// so the parser records the item list of the package that declares it, and
// none for the block at compilation-unit scope.
TEST(ExternalConstraintBlockParsing, ExternalBlockRecordsItsPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint proto1;\n"
      "  endclass\n"
      "  constraint C::proto1 { x > 0; }\n"
      "endpackage\n"
      "class D;\n"
      "  rand int y;\n"
      "  constraint proto1;\n"
      "endclass\n"
      "constraint D::proto1 { y > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 2u);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints[0].class_name, "C");
  EXPECT_EQ(r.cu->external_constraints[0].scope_items,
            &r.cu->packages[0]->items);
  EXPECT_EQ(r.cu->external_constraints[1].class_name, "D");
  EXPECT_EQ(r.cu->external_constraints[1].scope_items, nullptr);
}

// 18.5.1 with A.1.11: extern_constraint_declaration is a
// package_or_generate_item_declaration, which a module body reaches, so a
// block beside a class inside a module is read and records the module's items
// as its scope; the static form is read there too.
TEST(ExternalConstraintBlockParsing, ExternalBlockInAModuleRecordsTheModule) {
  auto r = Parse(
      "module m;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint p;\n"
      "    static constraint q;\n"
      "  endclass\n"
      "  constraint C::p { x > 0; }\n"
      "  static constraint C::q { x < 9; }\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->external_constraints.size(), 2u);
  EXPECT_EQ(r.cu->external_constraints[0].constraint_name, "p");
  EXPECT_EQ(r.cu->external_constraints[0].scope_items,
            &r.cu->modules[0]->items);
  EXPECT_EQ(r.cu->external_constraints[1].constraint_name, "q");
  EXPECT_TRUE(r.cu->external_constraints[1].is_static);
  EXPECT_EQ(r.cu->external_constraints[1].scope_items,
            &r.cu->modules[0]->items);
}

// 18.5.1 with A.1.11: a generate block holds package_or_generate_item
// declarations too, so a block beside a class in one records the generate
// block's items, the list that holds the class.
TEST(ExternalConstraintBlockParsing, ExternalBlockInAGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g\n"
      "    class C;\n"
      "      rand int x;\n"
      "      constraint p;\n"
      "    endclass\n"
      "    constraint C::p { x > 0; }\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  const auto* scope = r.cu->external_constraints[0].scope_items;
  ASSERT_NE(scope, nullptr);
  EXPECT_NE(scope, &r.cu->modules[0]->items);
  ASSERT_FALSE(scope->empty());
  EXPECT_EQ(scope->front()->kind, ModuleItemKind::kClassDecl);
  EXPECT_EQ(scope->front()->name, "C");
}

// 18.5.1: an external constraint block completes the prototype with the
// relations in its body. The parser captures each top-level relation so that
// elaboration can attach them to the prototype; a block with two relations
// records two, not the discarded body of before.
TEST(ExternalConstraintBlockParsing, ExternalBlockCapturesBodyRelations) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n"
      "constraint C::proto2 { x >= 0; x < 10; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints.front().body->constraint_exprs.size(),
            2u);
}

}  // namespace
