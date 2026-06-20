#include "fixture_elaborator.h"

namespace {

// §23.7.1 C3: a prefix that is not a resolvable scope name denotes the package
// scope resolution operator; the qualified type resolves downward in pkg.
TEST(ScopeResolutionPrefixElaboration, PackagePrefixResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module t;\n"
             "  pkg::byte_t x;\n"
             "endmodule\n"));
}

// §23.7.1 C2: a prefix that resolves by the normal scope rules (a visible class
// name) denotes the class scope resolution operator; the qualified type
// resolves downward in the class.
TEST(ScopeResolutionPrefixElaboration, ClassPrefixResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module t;\n"
             "  C::my_type x;\n"
             "endmodule\n"));
}

}  // namespace
