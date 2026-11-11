#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstructorElaboration, ExplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer command;\n"
             "  function new();\n"
             "    command = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "  function new(int cmd, int addr);\n"
             "    command = cmd;\n"
             "    address = addr;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new(1, 2);\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithDefaultArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  bit [12:0] address;\n"
             "  int cmd_time;\n"
             "  function new(int cmd = 0, bit [12:0] adrs = 0, int t = 0);\n"
             "    command = cmd;\n"
             "    address = adrs;\n"
             "    cmd_time = t;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorDerivedElaborates) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, PropertyWithExplicitDefaultElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x = 5;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, LocalConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  local function new();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ProtectedConstructorAccessibleToSubclass) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int b;\n"
             "  protected function new();\n"
             "    b = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int c;\n"
             "  function new();\n"
             "    super.new();\n"
             "    c = 2;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child ch;\n"
             "  initial ch = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithTimingControlError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "    #5 x = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
}

TEST(ClassConstructorElaboration, ConstructorWithEventControlError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  int y;\n"
      "  function new();\n"
      "    @(y) x = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 5,
      "13.4"));
}

TEST(ClassConstructorElaboration, ConstructorStatementThatCanBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x; event a, b, e;\n"
      "  function new();\n"
      "    wait (x == 1);\n"
      "    fork x = 1; join\n"
      "    fork x = 2; join_any\n"
      "    wait_order (a, b);\n"
      "    fork #1 x = 3; join_none\n"
      "    -> e;\n"
      "    x = f();\n"
      "    return;\n"
      "  endfunction\n"
      "  function int f(); return 2; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  class M;\n"
      "    int x, y;\n"
      "    function new(); @(y) x = 1; endfunction\n"
      "  endclass\n"
      "  C c;\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {4u, 7u, 18u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "time-controlling statement is not allowed inside a function", kLine,
        "13.4"))
        << kLine;
  }
  for (const uint32_t kLine : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "only fork/join_none is permitted inside a "
                              "function",
                              kLine, "13.4"))
        << kLine;
  }
  for (const uint32_t kLine : {8u, 9u, 10u, 11u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(ClassConstructorElaboration,
     DISABLED_ConstructorOfAPackageClassThatCanBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "package k;\n"
      "  class P;\n"
      "    int x, y;\n"
      "    function new();\n"
      "      #1 x = 1;\n"
      "      @(y) x = 2;\n"
      "      fork #1 x = 3; join_none\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "time-controlling statement is not allowed inside a function", kLine,
        "13.4"))
        << kLine;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 7));
}

TEST(ClassConstructorElaboration, DISABLED_ConstructorEnablingATaskIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  task t(); endtask\n"
      "  function new();\n"
      "    t();\n"
      "    this.t();\n"
      "    fork t(); join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  class M;\n"
      "    task kt(); endtask\n"
      "    function new(); kt(); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {4u, 5u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "function cannot enable a task", kLine, "13.4"))
        << kLine;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 6));
}

TEST(ClassConstructorElaboration,
     DISABLED_ConstructorReturningAValueIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  function new(int a);\n"
      "    if (a) return;\n"
      "    return 5;\n"
      "  endfunction\n"
      "endclass\n"
      "package k;\n"
      "  class P; function new(); return 1; endfunction endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class M; function new(); return 2; endfunction endclass\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {5u, 9u, 12u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), "returns a value", kLine, "8.7"))
        << kLine;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 4));
}

}  // namespace
