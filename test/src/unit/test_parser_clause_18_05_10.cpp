// §18.5.10: Static constraint blocks

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// package_or_generate_item_declaration: static extern_constraint_declaration
TEST(SourceText, PackageItemStaticExternConstraint) {
  auto r = Parse(
      "package pkg;\n"
      "  static constraint MyClass::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

using CheckerParseTest = ProgramTestParse;

// extern_constraint_declaration with static and dynamic_override_specifiers
TEST(SourceText, ExternConstraintDeclStaticOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern static constraint c;\n"
      "endclass\n"
      "static constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
