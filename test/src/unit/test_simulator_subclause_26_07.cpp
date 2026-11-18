#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfNamesTheRunningProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] non_null, same;\n"
      "  initial begin\n"
      "    automatic std::process p = std::process::self();\n"
      "    automatic process q = process::self();\n"
      "    non_null = (p != null) ? 1 : 0;\n"
      "    same = (p == q) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"non_null", 1u}, {"same", 1u}});
}

TEST(StdBuiltInPackageSim, StdQualifiedProcessHandleStatusAndStateLiterals) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] st, lits;\n"
      "  initial begin\n"
      "    automatic std::process p = std::process::self();\n"
      "    st = p.status();\n"
      "    lits = std::process::RUNNING + 10 * std::process::KILLED;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"st", 1u}, {"lits", 41u}});
}

TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfHandleKillsTheChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    std::process p;\n"
      "    x = 7;\n"
      "    fork\n"
      "      begin\n"
      "        p = std::process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(StdBuiltInPackageSim, ModuleLevelStdProcessStateVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  std::process::state ms;\n"
                       "  initial begin\n"
                       "    std::process::state ls;\n"
                       "    ms = std::process::FINISHED; "
                       "ls = std::process::RUNNING;\n"
                       "    $display(\"%s %s\", ms.name(), ls.name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "FINISHED RUNNING\n");
}

TEST(StdPackageSim, ProceduralStdSemaphoreHoldsTheBuiltinObject) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int a, b;\n"
                       "  initial begin\n"
                       "    automatic std::semaphore s = new(1);\n"
                       "    a = s.try_get(1);\n"
                       "    b = s.try_get(1);\n"
                       "    $display(\"a=%0d b=%0d\", a, b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=1 b=0\n");
}

TEST(StdPackageSim, ProceduralStdMailboxHoldsTheBuiltinObject) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int n, ok, v;\n"
                       "  initial begin\n"
                       "    automatic std::mailbox m = new;\n"
                       "    m.put(23);\n"
                       "    n = m.num();\n"
                       "    ok = m.try_get(v);\n"
                       "    $display(\"n=%0d ok=%0d v=%0d\", n, ok, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 ok=1 v=23\n");
}

TEST(StdPackageSim, StdSemaphoreBesideAUserClassIsTheBuiltin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  class semaphore;\n"
                 "    int keys;\n"
                 "    function new(int k = 0); keys = k + 40; endfunction\n"
                 "  endclass\n"
                 "  std::semaphore s = new(1);\n"
                 "  semaphore u = new(2);\n"
                 "  int a, b;\n"
                 "  initial begin\n"
                 "    a = s.try_get(1);\n"
                 "    b = s.try_get(1);\n"
                 "    $display(\"a=%0d b=%0d u=%0d\", a, b, u.keys);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "a=1 b=0 u=42\n");
}

TEST(StdPackageSim, StdMailboxBesideAUserClassIsTheBuiltin) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  class mailbox;\n"
                       "    int n = 5;\n"
                       "  endclass\n"
                       "  std::mailbox m = new;\n"
                       "  int n, v;\n"
                       "  initial begin\n"
                       "    m.put(31);\n"
                       "    n = m.num();\n"
                       "    void'(m.try_get(v));\n"
                       "    $display(\"n=%0d v=%0d\", n, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 v=31\n");
}

void ExpectStdOutput(const std::string& src, const std::string& expected) {
  SCOPED_TRACE(src);
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), expected);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StdPackageSim, AnUnqualifiedStdFunctionIsCalledFromAModule) {
  ExpectStdOutput(
      "module top; int x, r; initial begin r = randomize(x); "
      "$display(\"%0d\", r); end endmodule\n",
      "1\n");
}

TEST(StdPackageSim, AnUnqualifiedStdClassIsDeclaredInTheUnit) {
  ExpectStdOutput(
      "semaphore g = new(1);\n"
      "module top; initial $display(\"%0d %0d\", g.try_get(), g.try_get()); "
      "endmodule\n",
      "1 0\n");
}

TEST(StdPackageSim, AnExplicitStdImportInAPackageAndTheUnit) {
  ExpectStdOutput(
      "package pk; import std::*; semaphore s = new(1); endpackage\n"
      "import std::*;\n"
      "module top; initial $display(\"%0d %0d\", pk::s.try_get(), "
      "pk::s.try_get()); endmodule\n",
      "1 0\n");
}

TEST(StdPackageSim, AUserClassNamedForAStdClassInAnInterfaceOrProgram) {
  ExpectStdOutput(
      "interface ifc; class semaphore; int v = 5; endclass semaphore s = new; "
      "initial $display(\"i %0d\", s.v); endinterface\n"
      "program pg; class mailbox; int v = 6; endclass mailbox m = new; "
      "initial $display(\"p %0d\", m.v); endprogram\n"
      "module top; ifc u(); pg q(); endmodule\n",
      "i 5\np 6\n");
}

TEST(StdPackageSim, DISABLED_AUserClassNamedProcessTakesPrecedence) {
  ExpectStdOutput(
      "class process; int v = 8; endclass\n"
      "module top; process s = new; initial $display(\"%0d\", s.v); "
      "endmodule\n",
      "8\n");
  ExpectStdOutput(
      "package pp; class process; int v = 9; endclass endpackage\n"
      "module top; pp::process s = new; initial $display(\"%0d\", s.v); "
      "endmodule\n",
      "9\n");
  ExpectStdOutput(
      "interface ifc; class process; int v = 10; endclass process s = new; "
      "initial $display(\"%0d\", s.v); endinterface\n"
      "module top; ifc u(); endmodule\n",
      "10\n");
  ExpectStdOutput(
      "program pg; class process; int v = 11; endclass process s = new; "
      "initial $display(\"%0d\", s.v); endprogram\n"
      "module top; pg u(); endmodule\n",
      "11\n");
  ExpectStdOutput(
      "module top; class process; int v = 12; endclass process s = new; "
      "initial $display(\"%0d\", s.v); endmodule\n",
      "12\n");
}

TEST(StdPackageSim, DISABLED_AUserFunctionNamedRandomizeTakesPrecedence) {
  ExpectStdOutput(
      "module top; function int randomize(int a); return 77; endfunction "
      "int x, r; initial begin r = randomize(x); $display(\"%0d\", r); end "
      "endmodule\n",
      "77\n");
}

TEST(StdPackageSim, AStdScopedNameReachesTheBuiltinBesideAUserDeclaration) {
  ExpectStdOutput(
      "class semaphore; int v = 5; endclass\n"
      "module top; std::semaphore s = new(1); "
      "initial $display(\"%0d %0d\", s.try_get(), s.try_get()); endmodule\n",
      "1 0\n");
  ExpectStdOutput(
      "package up; class semaphore; int v = 5; endclass endpackage\n"
      "module top; import up::*; std::semaphore s = new(1); "
      "initial $display(\"%0d %0d\", s.try_get(), s.try_get()); endmodule\n",
      "1 0\n");
  ExpectStdOutput(
      "module top; function int randomize(int a); return 77; endfunction "
      "int x, r; initial begin r = std::randomize(x); $display(\"%0d\", r); "
      "end endmodule\n",
      "1\n");
}

TEST(StdPackageSim, AStdScopedTypeInEachScope) {
  ExpectStdOutput(
      "std::semaphore g = new(1);\n"
      "interface ifc; std::mailbox #(int) mb = new; int v; "
      "initial begin mb.put(4); mb.get(v); $display(\"i %0d\", v); end "
      "endinterface\n"
      "class C; std::semaphore s; function new(); s = new(1); endfunction "
      "endclass\n"
      "module top; ifc u(); C c = new; initial begin "
      "$display(\"u %0d %0d\", g.try_get(), g.try_get()); "
      "$display(\"c %0d %0d\", c.s.try_get(), c.s.try_get()); end endmodule\n",
      "u 1 0\nc 1 0\ni 4\n");
  ExpectStdOutput(
      "program pg; std::semaphore s = new(1); "
      "initial $display(\"%0d %0d\", s.try_get(), s.try_get()); endprogram\n"
      "module top; pg q(); endmodule\n",
      "1 0\n");
}

TEST(StdPackageSim, ADollarPrefixedStdFunctionNameIsReported) {
  SimFixture f;
  RunCapture(
      "module top; int x, r;\n"
      "initial r = $randomize(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$randomize is not a system task or system function", 2, "20.1"));
}

}  // namespace
