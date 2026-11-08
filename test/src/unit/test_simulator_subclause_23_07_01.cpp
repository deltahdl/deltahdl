#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
