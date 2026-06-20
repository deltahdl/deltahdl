#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §23.7.1 C1 (class operator): a ::-prefixed name resolves downward into the
// class scope and is never subject to the upward/local resolution rules of
// §23.8 — Base::x reads the class static (10), not the same-named local (999).
TEST(ScopeResolutionPrefixSim, PrefixDoesNotResolveToLocalVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static int x = 10;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int x = 999;\n"
                      "  int result;\n"
                      "  initial result = Base::x;\n"
                      "endmodule\n",
                      "result"),
            10u);
}

// §23.7.1 C1 (package operator): the package-qualified name resolves downward
// in the package and ignores the same-named module-level variable — pkg::N is
// 5, not the local 999.
TEST(ScopeResolutionPrefixSim, PackagePrefixDoesNotResolveToLocalVariable) {
  EXPECT_EQ(RunAndGet("package pkg;\n"
                      "  parameter int N = 5;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int N = 999;\n"
                      "  int result;\n"
                      "  initial result = pkg::N;\n"
                      "endmodule\n",
                      "result"),
            5u);
}

}  // namespace
