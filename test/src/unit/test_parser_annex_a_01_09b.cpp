// Observing tests for IEEE 1800-2023 Annex A.1.9 "Class items", continued from
// test_parser_annex_a_01_09a.cpp: a nettype_declaration as a class_property,
// and as no interface_class_item.

#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

// A.1.9 writes a class_property as { property_qualifier } data_declaration,
// and A.2.1.3 counts a nettype_declaration among data_declaration's forms, so
// a class body declares a nettype, a property qualifier before it included.
// Each is carried as a typedef member is, over the item
// Parser::ParseNettypeDecl returns, and the property after them is read as it
// would be without them.
TEST(ClassItems, ClassPropertyMayBeANettypeDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  nettype logic [3:0] nt;\n"
      "  static nettype real rt;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1U);
  const auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3U);
  for (int i = 0; i < 2; ++i) {
    EXPECT_EQ(members[i]->kind, ClassMemberKind::kTypedef);
    EXPECT_EQ(members[i]->typedef_item->kind, ModuleItemKind::kNettypeDecl);
  }
  EXPECT_EQ(members[0]->name, "nt");
  EXPECT_EQ(members[1]->name, "rt");
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[2]->name, "x");
}

// A nettype in a class takes the property qualifiers a class_property takes,
// and a method qualifier is no qualifier of it.
TEST(ClassItems, NettypeDeclarationAdmitsNoMethodQualifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual nettype bit nb;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'virtual' is no qualifier of a nettype declaration", 2,
      "A.1.9"));
}

// interface_class_item takes a type_declaration and none of data_declaration's
// other forms, so a nettype in an interface class is reported, and the typedef
// beside it is not.
TEST(ClassItems, NettypeDeclarationIsNoInterfaceClassItem) {
  auto r = Parse(
      "interface class I;\n"
      "  nettype logic [3:0] nt;\n"
      "  typedef int t;\n"
      "endclass\n");
  const char* msg = "a nettype declaration is no item of an interface class";
  EXPECT_TRUE(ReportedError(r.diags, msg, 2, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, msg, 3, "A.1.9"));
}

}  // namespace
