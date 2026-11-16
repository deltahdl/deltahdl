#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(LocalScopeResolutionCases, ARestrictedBlockReadsTheCallersListedName) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand int x;\n"
                   "endclass\n"
                   "module t;\n"
                   "  function int F(C obj, int x);\n"
                   "    return obj.randomize() with (x) { x == local::x; };\n"
                   "  endfunction\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    int ok;\n"
                   "    ok = F(c, 7);\n"
                   "    $display(\"%0d %0d\", ok, c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 7\n");
}

TEST(LocalScopeResolutionCases, LocalQualifiesAClassScope) {
  EXPECT_EQ(RunSrc("class P;\n"
                   "  static int v = 11;\n"
                   "endclass\n"
                   "class C;\n"
                   "  rand int x;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    void'(c.randomize() with { x == local::P::v; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "11\n");
}

TEST(LocalScopeResolutionCases, LocalReachesAWildcardImportPastAMember) {
  EXPECT_EQ(RunSrc("package p;\n"
                   "  int a = 4;\n"
                   "endpackage\n"
                   "class C;\n"
                   "  rand int x;\n"
                   "  int a = 40;\n"
                   "endclass\n"
                   "module t;\n"
                   "  import p::*;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    void'(c.randomize() with { x == local::a; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "4\n");
}

}  // namespace
