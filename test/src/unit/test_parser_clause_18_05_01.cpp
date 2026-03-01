// §18.5.1: External constraint blocks

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// package_or_generate_item_declaration: extern_constraint_declaration
TEST(SourceText, PackageItemExternConstraint) {
  auto r = Parse(
      "package pkg;\n"
      "  constraint MyClass::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

}  // namespace
