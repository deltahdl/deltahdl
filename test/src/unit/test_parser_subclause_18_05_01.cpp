#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

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
