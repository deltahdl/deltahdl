// §26.2: Package declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM §3.9 — Packages
// =============================================================================
// §3.9: "Packages provide a declaration space, which can be shared by other
//        building blocks." Package with typedef, functions, and end label.
TEST(ParserClause03, Cl3_9_PackageDeclarationsAndEndLabel) {
  auto r = ParseWithPreprocessor(
      "package ComplexPkg;\n"
      "  typedef struct { shortreal i, r; } Complex;\n"
      "  function automatic int helper(int x); return x; endfunction\n"
      "endpackage : ComplexPkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "ComplexPkg");
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kTypedef));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

}  // namespace
