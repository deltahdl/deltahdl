#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PackedAndUnpackedArraySim, DimensionsBeforeTheNameArePackedAfterUnpacked) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  bit [7:0] c1; real u [7:0]; bit [1:0][3:0] p;\n"
                 "  initial begin\n"
                 "    c1 = 8'hA5; u[3] = 1.5; u[7] = 2.5; p = 8'h5a;\n"
                 "    $display(\"%0d %0d %h %f %f %h %h %0d\", $bits(c1), "
                 "$size(u), c1, u[3], u[7], p[1], p[0], "
                 "$dimensions(p));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "8 8 a5 1.500000 2.500000 5 a 2\n");
}

TEST(PackedAndUnpackedArraySim, UnpackedArrayHoldsElementsOfAnyDataType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  class K; int v; function new(int x); v = x; endfunction endclass\n"
          "  typedef struct {int a; string s;} s_t;\n"
          "  bit [3:0] pa [2]; int ua [2][3]; string sa [2]; K ka [2];\n"
          "  s_t st [2]; int da [2][]; int qa [2][$]; event ea [2];\n"
          "  chandle ca [2];\n"
          "  initial begin\n"
          "    pa[1] = 4'hc; ua[1][2] = 7; sa[1] = \"hi\"; ka[1] = new(9);\n"
          "    st[1] = '{3, \"yo\"}; da[1] = new[3]; da[1][2] = 8;\n"
          "    qa[1].push_back(6); qa[1].push_back(5);\n"
          "    $display(\"%h %0d %s %0d %0d %s %0d %0d %0d %0d %0d\", pa[1], "
          "ua[1][2], sa[1], ka[1].v, st[1].a, st[1].s, da[1].size(), "
          "da[1][2], qa[1].size(), qa[1][1], ca[0] == null);\n"
          "    fork begin @(ea[1]); $display(\"ev\"); end begin #1 ->ea[1]; "
          "end join\n"
          "  end\n"
          "endmodule\n",
          f),
      "c 7 hi 9 3 yo 3 8 2 5 1\nev\n");
}

TEST(PackedAndUnpackedArraySim, EveryKindOfUnpackedArrayHoldsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; logic [1:0] b;} s_t;\n"
                       "  bit [7:0] d []; s_t m [int]; int q [$][2]; string "
                       "ds [];\n"
                       "  initial begin\n"
                       "    d = new[2]; d[1] = 8'h3c; m[5] = '{2, 2'b1x};\n"
                       "    ds = new[1]; ds[0] = \"z\"; q.push_back('{1, 2});\n"
                       "    $display(\"%h %0d %b %s %0d %0d\", d[1], m[5].a, "
                       "m[5].b, ds[0], q.size(), q[0][1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3c 2 1x z 1 2\n");
}

constexpr const char* kFourStateMember =
    "typedef struct { logic [2:0] k; int n; } lt;\n";

TEST(ArrayOfStructuresSim, DISABLED_FourStateMemberOfEachElementStartsAtX) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kFourStateMember) +
                           "package p; lt pa [2]; endpackage\n"
                           "interface I; lt ia [2]; endinterface\n"
                           "program P;\n"
                           "  lt pga [2];\n"
                           "  initial #1 $display(\"p %b\", pga[1].k);\n"
                           "endprogram\n"
                           "module t;\n"
                           "  I ii(); P pp();\n"
                           "  class C; lt ca [2]; endclass\n"
                           "  if (1) begin : g lt ga [2]; end\n"
                           "  lt a [4]; lt m [2][2]; C c;\n"
                           "  initial begin\n"
                           "    c = new;\n"
                           "    $display(\"%b %b %b %b %b %b\", a[0].k, "
                           "p::pa[0].k, c.ca[0].k, ii.ia[0].k, g.ga[0].k, "
                           "m[1][1].k);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "xxx xxx xxx xxx xxx xxx\np xxx\n");
}

TEST(ArrayOfStructuresSim, DISABLED_WholeElementCopiesKeepUnknownBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kFourStateMember) +
                           "module t;\n"
                           "  lt a [4]; lt m [2][2]; lt s; lt q [$];\n"
                           "  initial begin\n"
                           "    a[3] = '{3'b1x0, 5}; m[1][0].k = 3'bz1x;\n"
                           "    s = a[3]; q.push_back(a[3]);\n"
                           "    $display(\"%b %0d %b %b %b\", a[3].k, a[3].n, "
                           "m[1][0].k, s.k, q[0].k);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1x0 5 z1x 1x0 1x0\n");
}

}  // namespace
