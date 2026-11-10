#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StructureMemberKinds, ChandleMemberStartsNull) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  struct {chandle h; int x;} s;\n"
                       "  initial $display(\"%0d\", s.h == null);\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(StructureMemberKinds, DISABLED_EventMemberIsTriggeredAndWaitedOn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  struct {event e; int x;} s;\n"
                       "  initial fork\n"
                       "    begin @(s.e); $display(\"got %0t\", $time); end\n"
                       "    begin #1 ->s.e; end\n"
                       "  join\n"
                       "endmodule\n",
                       f),
            "got 1\n");
}

TEST(StructureMemberKinds,
     DISABLED_AssociativeArrayMemberIsWrittenAndReadByKey) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  struct {int a [string]; int x;} s;\n"
                       "  initial begin\n"
                       "    s.a[\"k\"] = 4; s.a[\"m\"] = 5;\n"
                       "    $display(\"%0d %0d %0d\", s.a[\"k\"], s.a[\"m\"], "
                       "s.a.num());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 5 2\n");
}

TEST(StructureMemberKinds, DISABLED_VirtualInterfaceMemberReachesItsInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface I; int w = 6; endinterface\n"
                 "module t;\n"
                 "  I ii();\n"
                 "  struct {virtual I vi; int x;} s;\n"
                 "  initial begin #1 s.vi = ii; $display(\"%0d\", s.vi.w); "
                 "end\n"
                 "endmodule\n",
                 f),
      "6\n");
}

TEST(InPlaceAggregateLocals, DISABLED_FunctionLocalsHoldTheirMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module t;\n"
                "  function automatic int fa();\n"
                "    struct packed {bit [7:0] p; bit [7:0] q;} FL;\n"
                "    struct {int a; int b;} UL;\n"
                "    union packed {bit [15:0] w; bit [15:0] v;} PU;\n"
                "    FL.p = 8'h5A; UL.b = 7; PU.v = 16'h1234;\n"
                "    $display(\"%h %0d %h %h\", FL.p, UL.b, PU.w, FL.p[3:0]);\n"
                "    return 0;\n"
                "  endfunction\n"
                "  function static int fs();\n"
                "    static struct {int a; int b;} UL = '{3, 4};\n"
                "    UL.a = UL.a + 10;\n"
                "    return UL.a;\n"
                "  endfunction\n"
                "  initial begin void'(fa()); $display(\"%0d\", fs()); end\n"
                "endmodule\n",
                f),
            "5a 7 1234 a\n13\n");
}

TEST(InPlaceAggregateLocals, MethodTaskAndBlockLocalsHoldTheirMembers) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    static function int sm();\n"
                 "      struct {int a; int b;} UL; UL.b = 9; return UL.b;\n"
                 "    endfunction\n"
                 "    function int im();\n"
                 "      struct {int a; int b;} UL; UL.a = 8; return UL.a;\n"
                 "    endfunction\n"
                 "  endclass\n"
                 "  task automatic tk(output int r);\n"
                 "    struct {int a; int b;} UL; UL.b = 2; r = UL.b;\n"
                 "  endtask\n"
                 "  C c; int r;\n"
                 "  initial begin\n"
                 "    c = new; tk(r);\n"
                 "    $display(\"%0d %0d %0d\", C::sm(), c.im(), r);\n"
                 "    begin : nb\n"
                 "      struct {int a; int b;} UL; UL.b = 12;\n"
                 "      $display(\"%0d\", UL.b);\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "9 8 2\n12\n");
}

constexpr const char* kScopedStructDecls =
    "typedef struct {int k; int u [2];} su_t;\n"
    "package pk;\n"
    "  parameter su_t P = '{1, '{20, 21}};\n"
    "  su_t v = '{2, '{30, 31}};\n"
    "endpackage\n"
    "parameter su_t UP = '{3, '{40, 41}};\n"
    "module t;\n"
    "  class C;\n"
    "    parameter su_t P = '{4, '{50, 51}};\n"
    "    static su_t v = '{5, '{60, 61}};\n"
    "  endclass\n"
    "  class D #(parameter su_t P = '{6, '{70, 71}}); endclass\n"
    "  parameter su_t MP = '{7, '{80, 81}};\n";

TEST(ScopedArrayMemberElement, ReadInAConstantExpression) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kScopedStructDecls) +
                     "  localparam int K1 = pk::P.u[0];\n"
                     "  localparam int K2 = C::P.u[1];\n"
                     "  localparam int K3 = MP.u[0];\n"
                     "  initial $display(\"%0d %0d %0d %0d\", K1, K2, K3, "
                     "$unit::UP.u[0]);\n"
                     "endmodule\n",
                 f),
      "20 51 80 40\n");
}

TEST(ScopedArrayMemberElement, DISABLED_ReadProcedurallyThroughAScopedName) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kScopedStructDecls) +
                           "  initial $display(\"%0d %0d %0d %0d %0d %0d\", "
                           "pk::P.u[0], pk::v.u[0], C::P.u[1], C::v.u[1], "
                           "D#()::P.u[1], pk::P.u[0][3:0]);\n"
                           "endmodule\n",
                       f),
            "20 30 51 61 71 4\n");
}

TEST(ArrayMemberOfStructureArray, DISABLED_ElementIsReadAndWrittenWhole) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct {int a; int b [4]; int c [3:0]; int d [1:4];} "
          "s_t;\n"
          "  typedef struct {int x; s_t s; string names [2];} o_t;\n"
          "  s_t arr [3]; s_t v1 [2][2]; o_t oa [2]; int i, j, k;\n"
          "  initial begin\n"
          "    foreach (arr[n]) begin\n"
          "      arr[n].a = n;\n"
          "      foreach (arr[n].b[m]) arr[n].b[m] = 10 * n + m;\n"
          "      foreach (arr[n].c[m]) arr[n].c[m] = 100 * n + m;\n"
          "      foreach (arr[n].d[m]) arr[n].d[m] = 1000 * n + m;\n"
          "    end\n"
          "    i = 2; k = 3;\n"
          "    $display(\"%0d %0d %0d %0d %0d\", arr[1].b[2], arr[i].b[k],\n"
          "             arr[2].c[3], arr[2].d[4], arr[1].d[1]);\n"
          "    v1[1][0].b[3] = 55; j = 0;\n"
          "    $display(\"%0d %0d\", v1[1][0].b[3], v1[i - 1][j].b[k]);\n"
          "    arr[1].b[2] = 99;\n"
          "    $display(\"%0d %0d %0d\", arr[1].b[2], arr[1].b[1], arr[1].a);\n"
          "    oa[1].s.b[2] = 7; oa[1].names[1] = \"hi\";\n"
          "    $display(\"%0d %s\", oa[1].s.b[2], oa[1].names[1]);\n"
          "    $display(\"%0d\", arr[1].b[9]);\n"
          "    arr[1].b[9] = 5;\n"
          "    $display(\"%0d %0d\", arr[1].b[3], arr[1].b[0]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "12 23 203 2004 1001\n55 55\n99 11 1\n7 hi\n0\n13 10\n");
}

TEST(ArrayMemberOfStructureArray, DISABLED_ElementInAPackageFunctionAndClass) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct {int b [4];} q_t;\n"
                       "package pk2; q_t pa [2]; endpackage\n"
                       "module t;\n"
                       "  function automatic int fn();\n"
                       "    q_t la [2];\n"
                       "    la[1].b[2] = 5;\n"
                       "    return la[1].b[2];\n"
                       "  endfunction\n"
                       "  class K; q_t ca [2]; endclass\n"
                       "  K h;\n"
                       "  initial begin\n"
                       "    h = new; pk2::pa[1].b[2] = 4; h.ca[1].b[2] = 6;\n"
                       "    $display(\"%0d %0d %0d\", pk2::pa[1].b[2], fn(), "
                       "h.ca[1].b[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 5 6\n");
}

TEST(InPlaceAggregateLocals, TypedefLocalOfAFunctionHoldsItsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} ab_t;\n"
                       "  function automatic int ft();\n"
                       "    ab_t UL; UL.b = 11; return UL.b;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d\", ft());\n"
                       "endmodule\n",
                       f),
            "11\n");
}

TEST(ScopedArrayMemberElement, ReadThroughAWildcardImport) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct {int k; int u [2];} su_t;\n"
                       "package pk; parameter su_t P = '{1, '{20, 21}}; "
                       "endpackage\n"
                       "module t;\n"
                       "  import pk::*;\n"
                       "  initial $display(\"%0d %0d\", P.u[0], P.u[1]);\n"
                       "endmodule\n",
                       f),
            "20 21\n");
}

}  // namespace
