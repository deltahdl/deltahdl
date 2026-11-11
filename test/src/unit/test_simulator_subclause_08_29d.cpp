#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

TEST(ClassGcSim, ObjectHeldInAProgramPackageOrUnitVariableSurvives) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "program p;\n"
        "  C h, z;\n"
        "  initial begin\n"
        "    h = new;\n"
        "    #10 $display(\"%0d\", h.x);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endprogram\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "package P;\n"
        "  C h;\n"
        "endpackage\n"
        "module m;\n"
        "  C o, l, z;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    P::h = o;\n"
        "    o = null;\n"
        "    #10 l = P::h;\n"
        "    $display(\"%0d\", l.x);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "C h;\n"
        "module m;\n"
        "  C z;\n"
        "  initial begin\n"
        "    h = new;\n"
        "    #10 $display(\"%0d\", h.x);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n");
  }
}

TEST(ClassGcSim, ObjectHeldInASuspendedSubroutineLocalSurvives) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "class D;\n"
        "  task t();\n"
        "    C c = new;\n"
        "    #10 $display(\"%0d\", c.x);\n"
        "  endtask\n"
        "endclass\n"
        "module m;\n"
        "  C z;\n"
        "  D d;\n"
        "  task automatic t();\n"
        "    C c = new;\n"
        "    #10 $display(\"%0d\", c.x);\n"
        "  endtask\n"
        "  initial t();\n"
        "  initial begin\n"
        "    d = new;\n"
        "    d.t();\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n7\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module m;\n"
        "  C obj, z;\n"
        "  task automatic use_obj(C c);\n"
        "    #10 $display(\"%0d\", c.x);\n"
        "  endtask\n"
        "  initial begin\n"
        "    obj = new;\n"
        "    fork\n"
        "      use_obj(obj);\n"
        "      use_obj(obj);\n"
        "    join_none\n"
        "    #1 obj = null;\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n7\n");
  }
}

TEST(ClassGcSim, ObjectHeldInAStaticLocalBetweenCallsSurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C z;\n"
      "  function void f(bit first);\n"
      "    static C s;\n"
      "    if (first) s = new;\n"
      "    else $display(\"%0d\", s.x);\n"
      "  endfunction\n"
      "  task tk(bit first);\n"
      "    static C s;\n"
      "    if (first) s = new;\n"
      "    else $display(\"%0d\", s.x);\n"
      "  endtask\n"
      "  initial begin\n"
      "    f(1);\n"
      "    tk(1);\n"
      "    #10 f(0);\n"
      "    tk(0);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7\n7\n");
}

TEST(ClassGcSim, ObjectHeldInASpecializationsStaticPropertySurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; function new(int v); x = v; endfunction endclass\n"
      "class S #(int N = 1); static C s; endclass\n"
      "module m;\n"
      "  C o, l2, l3, z;\n"
      "  initial begin\n"
      "    o = new(2);\n"
      "    S#(2)::s = o;\n"
      "    o = new(3);\n"
      "    S#(3)::s = o;\n"
      "    o = null;\n"
      "    #10 l2 = S#(2)::s;\n"
      "    l3 = S#(3)::s;\n"
      "    $display(\"%0d %0d\", l2.x, l3.x);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new(0); end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "2 3\n");
}

TEST(ClassGcSim, ObjectHeldThroughAnInterfaceClassHandleSurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "interface class I; pure virtual function int get(); endclass\n"
      "class C implements I; int x = 7; virtual function int get(); return x; "
      "endfunction endclass\n"
      "module m;\n"
      "  I h;\n"
      "  C c, z;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    h = c;\n"
      "    c = null;\n"
      "    #10 $display(\"%0d\", h.get());\n"
      "  end\n"
      "  initial begin\n"
      "    automatic I ah;\n"
      "    automatic C ac = new;\n"
      "    ah = ac;\n"
      "    ac = null;\n"
      "    #10 $display(\"%0d\", ah.get());\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7\n7\n");
}

TEST(ClassGcSim, ObjectHeldInANestedQueueSurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C z;\n"
      "  C q[$][$];\n"
      "  C mq[int][$];\n"
      "  initial begin\n"
      "    z = new;\n"
      "    q.push_back({z});\n"
      "    z = new;\n"
      "    mq[0] = {z};\n"
      "    z = null;\n"
      "    #10 $display(\"%0d %0d\", q[0][0].x, mq[0][0].x);\n"
      "  end\n"
      "  initial begin\n"
      "    automatic C aq[$][$];\n"
      "    automatic C amq[int][$];\n"
      "    automatic C t = new;\n"
      "    aq.push_back({t});\n"
      "    t = new;\n"
      "    amq[0] = {t};\n"
      "    t = null;\n"
      "    #10 $display(\"%0d %0d\", aq[0][0].x, amq[0][0].x);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7 7\n7 7\n");
}

TEST(ClassGcSim, DISABLED_ObjectHeldInANestedAssociativeArraySurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C z;\n"
      "  C m2[string][int];\n"
      "  initial begin\n"
      "    m2[\"k\"][0] = new;\n"
      "    #10 $display(\"%0d\", m2[\"k\"][0].x);\n"
      "  end\n"
      "  initial begin\n"
      "    automatic C am2[string][int];\n"
      "    am2[\"k\"][0] = new;\n"
      "    #10 $display(\"%0d\", am2[\"k\"][0].x);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7\n7\n");
}

TEST(ClassGcSim, ObjectHeldInAnObjectsContainerPropertySurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "class H; C q[$]; C m[int]; mailbox #(C) mb = new; endclass\n"
      "module m;\n"
      "  C z, g;\n"
      "  H h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    g = new;\n"
      "    h.q.push_back(g);\n"
      "    g = null;\n"
      "    h.m[0] = new;\n"
      "    begin\n"
      "      automatic C c = new;\n"
      "      void'(h.mb.try_put(c));\n"
      "    end\n"
      "    #10 void'(h.mb.try_get(g));\n"
      "    $display(\"%0d %0d %0d\", h.q[0].x, h.m[0].x, g.x);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7 7 7\n");
}

TEST(ClassGcSim,
     DISABLED_ObjectHeldInAStructureMemberSurvivesWhereverTheStructureIs) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "typedef struct { int i; C h; } st;\n"
        "module m;\n"
        "  C z;\n"
        "  st s;\n"
        "  initial begin\n"
        "    s.h = new;\n"
        "    #10 $display(\"%0d\", s.h.x);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "typedef struct { int i; C h; } st;\n"
        "class K; st p; static st sp; endclass\n"
        "module m;\n"
        "  C z;\n"
        "  K k;\n"
        "  st q[$];\n"
        "  st d[];\n"
        "  st a[int];\n"
        "  st nb;\n"
        "  st bl;\n"
        "  st t;\n"
        "  initial begin\n"
        "    automatic st al;\n"
        "    al.h = new;\n"
        "    k = new;\n"
        "    k.p.h = new;\n"
        "    K::sp.h = new;\n"
        "    t.h = new;\n"
        "    q.push_back(t);\n"
        "    t.h = new;\n"
        "    d = new[1];\n"
        "    d[0] = t;\n"
        "    t.h = new;\n"
        "    a[0] = t;\n"
        "    t.h = new;\n"
        "    nb <= #5 t;\n"
        "    t.h = new;\n"
        "    fork\n"
        "      bl = #5 t;\n"
        "    join_none\n"
        "    #1 t.h = null;\n"
        "    #9;\n"
        "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", al.h.x, k.p.h.x, "
        "K::sp.h.x, q[0].h.x, d[0].h.x, a[0].h.x, nb.h.x, bl.h.x);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7 7 7 7 7 7 7 7\n");
  }
}

TEST(ClassGcSim, ObjectReadAgainByAnFmonitorSurvivesItsCaller) {
  const std::string kPath = ::testing::TempDir() + "class_gc_fmonitor.txt";
  SimFixture f;
  RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C z;\n"
      "  int k;\n"
      "  int fd;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fmonitor(fd, \"%0d %0d\", c.x, k);\n"
          "  end\n"
          "  initial #10 k = 1;\n"
          "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
          "  initial #20 $fclose(fd);\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(SlurpFile(kPath), "7 0\n7 1\n");
  std::remove(kPath.c_str());
}

TEST(ClassGcSim, ObjectHeldInACheckerVariableSurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "checker ck;\n"
      "  C h = new;\n"
      "endchecker\n"
      "module m;\n"
      "  C z;\n"
      "  ck c1 ();\n"
      "  initial #10 $display(\"%0d\", c1.h.x);\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7\n");
}

}  // namespace
