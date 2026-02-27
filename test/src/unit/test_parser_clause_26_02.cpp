// §26.2: Package declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// description: package_declaration
TEST(SourceText, DescriptionPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

}  // namespace
