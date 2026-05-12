// §3.3

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.3 states that the module — the basic building block — is "enclosed
// between the keywords module and endmodule". Verify the parser accepts a
// declaration that opens with `module` and closes with `endmodule`, and that
// it builds the corresponding ModuleDecl with that exact decl_kind. Observing
// a populated cu->modules entry with kModule confirms ParseModuleDecl
// consumed both bracketing keywords on the success path.
TEST(ModuleEnclosure, ModuleEndmoduleKeywordsBracketDeclaration) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

// §3.3's enclosure rule binds both ends of the bracket: omitting `endmodule`
// must not parse as a well-formed module. Drive the parser at a source that
// opens `module m;` and ends before `endmodule`; the Expect(kKwEndmodule)
// call inside ParseModuleDecl is the production-code site that observes the
// rule, and it should raise a diagnostic the test sees as has_errors.
TEST(ModuleEnclosure, MissingEndmoduleIsRejected) {
  auto r = Parse("module m;\n");
  EXPECT_TRUE(r.has_errors);
}

// §3.3's bracket holds across the module's body: `endmodule` closes the
// declaration whether the body is empty or carries items. The
// ParseModuleBody loop only terminates at `endmodule` or EOF, so observing
// a clean parse on a module that carries an item proves the loop exited on
// the closing keyword rather than truncating early.
TEST(ModuleEnclosure, EndmoduleClosesModuleWithBody) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

// §3.3's bracket cannot be substituted by body content: a module that
// carries items but never reaches `endmodule` must still be rejected.
// Reaching EOF inside the body drops out of ParseModuleBody on AtEnd(),
// after which Expect(kKwEndmodule) sees EOF and raises the diagnostic.
TEST(ModuleEnclosure, BodyContentDoesNotSubstituteForEndmodule) {
  auto r = Parse("module m; wire w;\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
