#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

std::string Top(const std::string& assertion, const std::string& after = "") {
  return "class C;\n"
         "  int x = 5;\n"
         "  task t(input int v); $display(\"C.t %0d\", v); endtask\n"
         "  function void f(input int v); $display(\"C.f %0d\", v); "
         "endfunction\n"
         "endclass\n"
         "module top;\n"
         "  int s = 0; int arr [2] = '{10, 20}; int i = 0; int calls = 0;\n"
         "  C h = new;\n"
         "  task show(input int v); $display(\"show %0d\", v); endtask\n"
         "  function void vshow(input int v); $display(\"vshow %0d\", v); "
         "endfunction\n"
         "  function int dbl(input int v); return 2 * v; endfunction\n"
         "  function int next(); calls++; return calls; endfunction\n"
         "  initial begin\n"
         "    s = 1;\n"
         "    " +
         assertion +
         "\n"
         "    s = 9; i = 1; h.x = 7;\n" +
         after +
         "  end\n"
         "endmodule\n";
}

std::string Simulate(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
  return out;
}

struct Case {
  const char* assertion;
  const char* expected;
};

void ExpectEach(std::initializer_list<Case> cases) {
  for (const auto& c : cases) {
    EXPECT_EQ(Simulate(Top(c.assertion)), c.expected) << c.assertion;
  }
}

TEST(DeferredByValueActual, AFinalFormsActualIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assert final (1) show(dbl(s));", "show 2\n"},
              {"assert final (0) else show(dbl(s));", "show 2\n"},
              {"assert final (0) else show(s);", "show 1\n"}});
}

TEST(DeferredByValueActual, ASystemTaskArgumentIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assert #0 (0) else $display(\"sys %0d\", s);", "sys 1\n"},
              {"assert final (0) else $display(\"sys %0d\", s);", "sys 1\n"},
              {"assert #0 (1) $display(\"sys %0d\", s);", "sys 1\n"},
              {"assert final (1) $display(\"sys %0d\", s);", "sys 1\n"}});
}

TEST(DeferredByValueActual, ASeverityTaskArgumentIsTakenWhenTheAssertionRuns) {
  for (const char* assertion : {"assert #0 (0) else $error(\"e %0d\", s);",
                                "assert final (0) else $error(\"e %0d\", s);",
                                "assume #0 (0) else $error(\"e %0d\", s);"}) {
    SimFixture f;
    RunCapture(Top(assertion), f);
    EXPECT_EQ(f.ctx.LastSeverity(), "ERROR") << assertion;
    EXPECT_EQ(f.ctx.LastSeverityMsg(), "e 1") << assertion;
  }
}

TEST(DeferredByValueActual, AVoidFunctionsInputIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assert #0 (0) else vshow(s);", "vshow 1\n"},
              {"assert final (0) else vshow(s);", "vshow 1\n"},
              {"assert #0 (0) else vshow(dbl(s));", "vshow 2\n"},
              {"assert final (1) vshow(dbl(s));", "vshow 2\n"}});
}

TEST(DeferredByValueActual, AMethodsInputIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assert #0 (0) else h.t(s);", "C.t 1\n"},
              {"assert final (0) else h.t(s);", "C.t 1\n"},
              {"assert #0 (0) else h.f(s);", "C.f 1\n"},
              {"assert final (1) h.f(s);", "C.f 1\n"}});
}

TEST(DeferredByValueActual, AnAssumeOrCoverActualIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assume #0 (1) show(s);", "show 1\n"},
              {"assume final (1) show(s);", "show 1\n"},
              {"assume #0 (0) else show(s);", "show 1\n"},
              {"assume final (0) else $display(\"a %0d\", s);", "a 1\n"},
              {"cover #0 (1) show(s);", "show 1\n"},
              {"cover final (1) $display(\"c %0d\", s);", "c 1\n"}});
}

TEST(DeferredByValueActual, ASelectOrPropertyIsTakenWhenTheAssertionRuns) {
  ExpectEach({{"assert #0 (0) else $display(\"arr %0d\", arr[i]);", "arr 10\n"},
              {"assert final (0) else $display(\"hx %0d\", h.x);", "hx 5\n"}});
}

TEST(DeferredByValueActual, AnActualsFunctionCallRunsOnce) {
  for (const char* assertion :
       {"assert #0 (0) else show(next());", "assert final (1) show(next());"}) {
    EXPECT_EQ(
        Simulate(Top(assertion, "    #1 $display(\"calls %0d\", calls);\n")),
        "show 1\ncalls 1\n")
        << assertion;
  }
}

std::string StaticItem(const std::string& kind, const std::string& unit_open,
                       const std::string& unit_close,
                       const std::string& instance) {
  return "class C; int x = 5; endclass\n" + unit_open +
         "\n"
         "  logic c = 1; C h = new;\n"
         "  a: assert " +
         kind +
         " (c) else $display(\"%0d\", h.x);\n"
         "  initial begin #1 h.x = 3; c = 0; #0 h.x = 4; end\n" +
         unit_close + "\n" + instance;
}

TEST(DeferredByValueActual, AStaticAssertionsActualIsTakenWhenItRuns) {
  for (const char* kind : {"#0", "final"}) {
    EXPECT_EQ(Simulate(StaticItem(kind, "module top;", "endmodule", "")), "3\n")
        << kind;
    EXPECT_EQ(Simulate(StaticItem(kind, "interface ifc;", "endinterface",
                                  "module top; ifc i(); endmodule\n")),
              "3\n")
        << kind;
  }
}

TEST(DeferredByValueActual,
     DISABLED_ACheckersStaticAssertionsActualIsTakenWhenItRuns) {
  for (const char* kind : {"#0", "final"}) {
    EXPECT_EQ(Simulate(std::string("class C; int x = 5; endclass\n"
                                   "checker chk(logic c);\n"
                                   "  a: assert ") +
                       kind +
                       " (c) else $display(\"%0d\", top.h.x);\n"
                       "endchecker\n"
                       "module top;\n"
                       "  logic c = 1; C h = new;\n"
                       "  chk k(c);\n"
                       "  initial begin #1 h.x = 3; c = 0; #0 h.x = 4; end\n"
                       "endmodule\n"),
              "3\n")
        << kind;
  }
}

TEST(DeferredByValueActual, AStaticFunctionsFormalIsTakenAtEachCall) {
  for (const char* kind : {"#0", "final"}) {
    EXPECT_EQ(Simulate(std::string("module top;\n"
                                   "  function void show(input int v); "
                                   "$display(\"show %0d\", v); endfunction\n"
                                   "  function void chk(input int v); "
                                   "assert ") +
                       kind +
                       " (0) else show(v); endfunction\n"
                       "  initial begin chk(1); chk(2); end\n"
                       "endmodule\n"),
              "show 1\nshow 2\n")
        << kind;
  }
}

TEST(DeferredByValueActual, AClassMethodsFormalAndPropertyAreTakenWhenItRuns) {
  for (const char* kind : {"#0", "final"}) {
    EXPECT_EQ(Simulate(std::string("class C;\n"
                                   "  int x = 5;\n"
                                   "  function void m(input int v);\n"
                                   "    assert ") +
                       kind +
                       " (0) else $display(\"m %0d %0d\", v, x);\n"
                       "    x = 8; v = 9;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module top; C h = new; initial h.m(1); endmodule\n"),
              "m 1 5\n")
        << kind;
  }
}

}  // namespace
