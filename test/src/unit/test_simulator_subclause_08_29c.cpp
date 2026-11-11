#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ClassGcSim, UnreferencedCycleAndSelfReferenceAreReclaimed) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class N; N n; endclass\n"
        "module t;\n"
        "  N a, b, o, z;\n"
        "  weak_reference #(N) wa, wb, wo;\n"
        "  initial begin\n"
        "    a = new; b = new; a.n = b; b.n = a;\n"
        "    o = new; o.n = o;\n"
        "    wa = new(a); wb = new(b); wo = new(o);\n"
        "    a = null; b = null; o = null;\n"
        "    repeat (4) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d %0d %0d\", wa.get() == null, wb.get() == null, "
        "wo.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1 1 1\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class N; N n; endclass\n"
        "module t;\n"
        "  N z;\n"
        "  weak_reference #(N) wa, wb, wo;\n"
        "  initial begin\n"
        "    begin\n"
        "      automatic N a = new;\n"
        "      automatic N b = new;\n"
        "      automatic N o = new;\n"
        "      a.n = b; b.n = a; o.n = o;\n"
        "      wa = new(a); wb = new(b); wo = new(o);\n"
        "      a = null; b = null; o = null;\n"
        "    end\n"
        "    repeat (4) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d %0d %0d\", wa.get() == null, wb.get() == null, "
        "wo.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1 1 1\n");
  }
}

TEST(ClassGcSim, DISABLED_LocalOfAFinishedProcessOrReturnedTaskIsReclaimed) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module t;\n"
      "  C z;\n"
      "  weak_reference #(C) wp, wt;\n"
      "  task automatic make();\n"
      "    C c = new;\n"
      "    wt = new(c);\n"
      "  endtask\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    wp = new(c);\n"
      "  end\n"
      "  initial begin\n"
      "    make();\n"
      "    repeat (4) begin #1 repeat (50) z = new; end\n"
      "    $display(\"%0d %0d\", wp.get() == null, wt.get() == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 1\n");
}

TEST(ClassGcSim, LocalOfAProcessStoppedByDisableForkIsReclaimed) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module t;\n"
      "  C z;\n"
      "  weak_reference #(C) wf;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        automatic C c = new;\n"
      "        wf = new(c);\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1 disable fork;\n"
      "  end\n"
      "  initial begin\n"
      "    repeat (5) begin #1 repeat (50) z = new; end\n"
      "    $display(\"%0d\", wf.get() == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1\n");
}

TEST(ClassGcSim, DISABLED_LocalOfAKilledProcessOrDisabledBlockIsReclaimed) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module t;\n"
        "  C z;\n"
        "  process p;\n"
        "  weak_reference #(C) wk;\n"
        "  initial begin\n"
        "    fork\n"
        "      begin\n"
        "        automatic C c = new;\n"
        "        wk = new(c);\n"
        "        p = process::self();\n"
        "        #100;\n"
        "      end\n"
        "    join_none\n"
        "    #1 p.kill();\n"
        "  end\n"
        "  initial begin\n"
        "    repeat (5) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d %0d\", wk.get() == null, p.status() == "
        "process::KILLED);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1 1\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module t;\n"
        "  C z;\n"
        "  weak_reference #(C) wd;\n"
        "  initial begin\n"
        "    begin : blk\n"
        "      automatic C c = new;\n"
        "      wd = new(c);\n"
        "      #100;\n"
        "    end\n"
        "  end\n"
        "  initial #1 disable blk;\n"
        "  initial begin\n"
        "    repeat (5) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d\", wd.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n");
  }
}

TEST(ClassGcSim, DroppedShallowCopyIsReclaimed) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module t;\n"
      "  C a, b, z;\n"
      "  weak_reference #(C) w;\n"
      "  initial begin\n"
      "    a = new;\n"
      "    b = new a;\n"
      "    w = new(b);\n"
      "    b = null;\n"
      "    repeat (4) begin #1 repeat (50) z = new; end\n"
      "    $display(\"%0d %0d\", w.get() == null, a.x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 7\n");
}

TEST(ClassGcSim, DroppedBuiltInClassObjectsAreReclaimed) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module t;\n"
        "  C o, z;\n"
        "  mailbox m;\n"
        "  semaphore s;\n"
        "  weak_reference #(C) w;\n"
        "  weak_reference #(mailbox) wm;\n"
        "  weak_reference #(semaphore) ws;\n"
        "  weak_reference #(weak_reference #(C)) ww;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    m = new;\n"
        "    s = new;\n"
        "    w = new(o);\n"
        "    wm = new(m);\n"
        "    ws = new(s);\n"
        "    ww = new(w);\n"
        "    m = null;\n"
        "    s = null;\n"
        "    w = null;\n"
        "    repeat (4) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d %0d %0d\", wm.get() == null, ws.get() == null, "
        "ww.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1 1 1\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module t;\n"
        "  C z;\n"
        "  process p;\n"
        "  weak_reference #(process) wp;\n"
        "  initial begin\n"
        "    fork\n"
        "      begin\n"
        "        p = process::self();\n"
        "      end\n"
        "    join\n"
        "    wp = new(p);\n"
        "    p = null;\n"
        "    repeat (4) begin #1 repeat (50) z = new; end\n"
        "    $display(\"%0d\", wp.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n");
  }
}

TEST(ClassGcSim, DISABLED_IntegerEqualToAnObjectsIdDoesNotKeepIt) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module t;\n"
      "  C o, z;\n"
      "  longint k;\n"
      "  weak_reference #(C) w;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    w = new(o);\n"
      "    k = weak_reference #(C)::get_id(o);\n"
      "    o = null;\n"
      "    repeat (4) begin #1 repeat (50) z = new; end\n"
      "    $display(\"%0d %0d\", w.get() == null, k != 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 1\n");
}

TEST(ClassGcSim, PendingNonblockingAssignmentToAMemberKeepsItsObject) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
        "inner; task t(); x <= #5 3; endtask endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  weak_reference #(C) w, wi;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o.x <= #5 3;\n"
        "    o = null;\n"
        "  end\n"
        "  initial begin\n"
        "    #1 repeat (50) z = new;\n"
        "    #3 $display(\"%0d\", w.get() != null);\n"
        "    #2 $display(\"%0d\", w.get().x);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n3\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
        "inner; task t(); x <= #5 3; endtask endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  weak_reference #(C) w, wi;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o.t();\n"
        "    o = null;\n"
        "  end\n"
        "  initial begin\n"
        "    #1 repeat (50) z = new;\n"
        "    #3 $display(\"%0d\", w.get() != null);\n"
        "    #2 $display(\"%0d\", w.get().x);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n3\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
        "inner; task t(); x <= #5 3; endtask endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  weak_reference #(C) w, wi;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o.inner = new;\n"
        "    wi = new(o.inner);\n"
        "    o.inner.x <= #5 3;\n"
        "    o = null;\n"
        "  end\n"
        "  initial begin\n"
        "    #1 repeat (50) z = new;\n"
        "    #3 $display(\"%0d\", wi.get() != null);\n"
        "    #2 $display(\"%0d\", wi.get().x);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n3\n");
  }
}

TEST(ClassGcSim,
     DISABLED_PendingNonblockingAssignmentToASelectOfAMemberKeepsItsObject) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
      "inner; task t(); x <= #5 3; endtask endclass\n"
      "module m;\n"
      "  C o, z;\n"
      "  weak_reference #(C) w, wi;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    w = new(o);\n"
      "    o.a[1] <= #5 3;\n"
      "    o.v[3:0] <= #5 4'h1;\n"
      "    o = null;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 repeat (50) z = new;\n"
      "    #3 $display(\"%0d\", w.get() != null);\n"
      "    #2 $display(\"%0d\", w.get().a[1] * 10 + w.get().v[3:0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1\n31\n");
}

TEST(ClassGcSim, PendingAssignmentToAStaticPropertyOrALandedOneKeepsNothing) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
        "inner; task t(); x <= #5 3; endtask endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  weak_reference #(C) w, wi;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o.s <= #5 3;\n"
        "    o = null;\n"
        "  end\n"
        "  initial begin\n"
        "    #1 repeat (50) z = new;\n"
        "    #3 $display(\"%0d\", w.get() == null);\n"
        "    #2 $display(\"%0d\", C::s);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n3\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x; static int s; int a[2]; logic [7:0] v; int q[$]; C "
        "inner; task t(); x <= #5 3; endtask endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  weak_reference #(C) w;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o.x <= #5 3;\n"
        "    o = null;\n"
        "  end\n"
        "  initial begin\n"
        "    #7 repeat (50) z = new;\n"
        "    #1 $display(\"%0d\", w.get() == null);\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n");
  }
}

TEST(ClassGcSim, ObjectReturnedByAnAutomaticFunctionSurvives) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; static function C make(); C r = new; return r; "
      "endfunction endclass\n"
      "module m;\n"
      "  C h1, h2, h3, z;\n"
      "  function automatic C make1(); C r = new; return r; endfunction\n"
      "  function automatic C make3(); make3 = new; endfunction\n"
      "  initial begin\n"
      "    h1 = make1();\n"
      "    h2 = C::make();\n"
      "    h3 = make3();\n"
      "    #10 $display(\"%0d %0d %0d\", h1.x, h2.x, h3.x);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "7 7 7\n");
}

TEST(ClassGcSim, WeakReferenceKeepsNothingWhereverItIsHeld) {
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "module m;\n"
        "  C o, h, z;\n"
        "  weak_reference #(C) w;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    w = new(o);\n"
        "    o = null;\n"
        "    h = w.get();\n"
        "    #10 $display(\"%0d %0d\", h.x, w.get() == h);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "7 1\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; endclass\n"
        "class H; weak_reference #(C) w; endclass\n"
        "module m;\n"
        "  C o, z;\n"
        "  H h;\n"
        "  initial begin\n"
        "    h = new;\n"
        "    o = new;\n"
        "    h.w = new(o);\n"
        "    o = null;\n"
        "    #10 $display(\"%0d\", h.w.get() == null);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "1\n");
  }
  {
    SimFixture f;
    std::string out = RunCapture(
        "class C; int x = 7; C b; endclass\n"
        "module m;\n"
        "  C a, z;\n"
        "  weak_reference #(C) w, wb;\n"
        "  int r1;\n"
        "  initial begin\n"
        "    a = new;\n"
        "    a.b = new;\n"
        "    a.b.x = 8;\n"
        "    w = new(a);\n"
        "    wb = new(a.b);\n"
        "    a = null;\n"
        "    r1 = w.get().b.x;\n"
        "    #10 $display(\"%0d %0d %0d\", r1, w.get() == null, wb.get() == "
        "null);\n"
        "  end\n"
        "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
        "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    EXPECT_EQ(out, "8 1 1\n");
  }
}

TEST(ClassGcSim,
     DISABLED_WeakReferenceInAQueueElementIsClearedWithItsReferent) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C o, z;\n"
      "  weak_reference #(C) wq[$];\n"
      "  weak_reference #(C) t;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    t = new(o);\n"
      "    wq.push_back(t);\n"
      "    t = null;\n"
      "    o = null;\n"
      "    #10 $display(\"%0d\", wq[0].get() == null);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1\n");
}

TEST(ClassGcSim, DISABLED_HeldBuiltInReferentIsNotCleared) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  C o, z;\n"
      "  weak_reference #(C) w1;\n"
      "  weak_reference #(weak_reference #(C)) w2;\n"
      "  mailbox #(int) mb;\n"
      "  semaphore s;\n"
      "  weak_reference #(mailbox #(int)) wm;\n"
      "  weak_reference #(semaphore) ws;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    w1 = new(o);\n"
      "    w2 = new(w1);\n"
      "    mb = new;\n"
      "    s = new;\n"
      "    wm = new(mb);\n"
      "    ws = new(s);\n"
      "    #10 $display(\"%0d %0d %0d\", w2.get() == w1, wm.get() == mb, "
      "ws.get() == s);\n"
      "  end\n"
      "  initial repeat (5) begin #1 repeat (50) z = new; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 1 1\n");
}

}  // namespace
