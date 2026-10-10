#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// --- What a resolution function may do with its argument (§6.6.7) ---

// The function shall neither write any part of its driver array nor resize it.
TEST(NettypeElaboration, ResolutionFunctionWritingItsDriverArrayRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    d[0] = 4'h0;\n"
      "    return d[1];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' writes to or resizes "
                            "its driver array 'd'",
                            3, "6.6.7"));
}

TEST(NettypeElaboration, ResolutionFunctionResizingItsDriverArrayRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    logic [3:0] r = d[0];\n"
      "    d.delete();\n"
      "    return r;\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' writes to or resizes "
                            "its driver array 'd'",
                            4, "6.6.7"));
}

// The function shall have no side effects, and a write to a variable it does
// not declare is one: the count would depend on how often the simulator
// resolves the net. The write is reported whether it is an increment or one
// name of a concatenation on an assignment's left side.
TEST(NettypeElaboration, ResolutionFunctionWritingAModuleVariableRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    logic [3:0] r = '0;\n"
      "    calls++;\n"
      "    {r, calls} = {r, calls};\n"
      "    foreach (d[i]) r |= d[i];\n"
      "    return r;\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' has a side effect: it "
                            "writes 'calls'",
                            5, "6.6.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' has a side effect: it "
                            "writes 'calls'",
                            6, "6.6.7"));
}

// The counterpart, the clause's own Tsum: it writes its local result through
// the function's name and a member of it, inside a foreach over the drivers,
// and reads the driver array alone. None of that is a write the rule forbids.
TEST(NettypeElaboration, ResolutionFunctionWritingOnlyItsOwnResultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function automatic T Tsum(input T driver[]);\n"
      "    real acc;\n"
      "    acc = 0.0;\n"
      "    Tsum.field1 = 0.0;\n"
      "    foreach (driver[i]) Tsum.field1 += driver[i].field1;\n"
      "  endfunction\n"
      "  nettype T wTsum with Tsum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A nonblocking assignment and a decrement write as an assignment and an
// increment do, so either one to a module variable is a side effect.
TEST(NettypeElaboration,
     ResolutionFunctionNonblockingOrDecrementWriteRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    calls <= 1;\n"
      "    --calls;\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4U, 5U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "resolution function 'res' has a side effect: "
                              "it writes 'calls'",
                              line, "6.6.7"));
  }
}

// A call written as a statement writes nothing the rule names unless it is
// one of the methods that change an array in place: a system task, a plain or
// a package-scoped subroutine, and a method of another name all pass.
TEST(NettypeElaboration, ResolutionFunctionCallingWithoutWritingAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  function automatic void note(logic [3:0] v);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  class C;\n"
      "    function void peek();\n"
      "    endfunction\n"
      "  endclass\n"
      "  function automatic void note(logic [3:0] v);\n"
      "  endfunction\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    C c = new;\n"
      "    $display(\"%h\", d[0]);\n"
      "    note(d[0]);\n"
      "    p::note(d[0]);\n"
      "    c.peek();\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A function with no argument has no driver array whose writes the body could
// be judged by; the count of its arguments is what is reported.
TEST(NettypeElaboration, ResolutionFunctionWithoutAnArgumentReportsItsCount) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  function logic res();\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  nettype logic nt with res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall take a single input argument", 5, "6.6.7"));
}

// A write through a package, a class scope, `$unit` or `$root` reaches
// something outside the function whatever the function declares, so each one
// is a side effect, named as it is written. The local `u` does not hide
// `$unit::u`.
TEST(NettypeElaboration, ResolutionFunctionWritingThroughAScopeRejected) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  int calls;\n"
      "  int q[$];\n"
      "endpackage\n"
      "int u;\n"
      "module m;\n"
      "  class C;\n"
      "    static int n;\n"
      "  endclass\n"
      "  int calls;\n"
      "  function automatic logic [3:0] res(input logic [3:0] d[]);\n"
      "    int u;\n"
      "    p::calls = 1;\n"
      "    C::n++;\n"
      "    p::q.delete();\n"
      "    $unit::u = 1;\n"
      "    $root.m.calls[0] = 1'b1;\n"
      "    return d[0];\n"
      "  endfunction\n"
      "  nettype logic [3:0] nt with res;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string> kWrites[] = {{13, "p::calls"},
                                                      {14, "C::n"},
                                                      {15, "p::q"},
                                                      {16, "$unit::u"},
                                                      {17, "$root.m.calls"}};
  for (const auto& [line, name] : kWrites) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "resolution function 'res' has a side effect: "
                              "it writes '" +
                                  name + "'",
                              line, "6.6.7"));
  }
}

}  // namespace
