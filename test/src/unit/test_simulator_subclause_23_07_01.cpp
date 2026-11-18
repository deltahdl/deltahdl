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

TEST(ScopeResolutionPrefixSim,
     DISABLED_AUnitClassComesBeforeALikeNamedPackage) {
  EXPECT_EQ(RunAndGet("package C;\n  int v = 1;\nendpackage\n"
                      "class C;\n  static int v = 2;\nendclass\n"
                      "module t;\n  int result;\n  initial result = C::v;\n"
                      "endmodule\n",
                      "result"),
            2u);
}

TEST(ScopeResolutionPrefixSim,
     DISABLED_AnImportedClassComesBeforeALikeNamedPackage) {
  EXPECT_EQ(RunAndGet("package K;\n  int v = 1;\nendpackage\n"
                      "package p;\n  class K;\n    static int v = 2;\n"
                      "  endclass\nendpackage\n"
                      "module t;\n  import p::*;\n  int result;\n"
                      "  initial result = K::v;\nendmodule\n",
                      "result"),
            2u);
}

}  // namespace
