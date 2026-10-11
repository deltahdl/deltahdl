#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §10.4.2: a nonblocking assignment to an automatic variable is illegal, and a
// function's locals are automatic in an automatic function.
TEST(NonblockingAutomaticTarget, AutomaticFunctionLocalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function automatic void fn();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 4,
                            "10.4.2"));
}

// §8.6 makes every method of a class automatic, so its locals are automatic
// whatever the declaration says.
TEST(NonblockingAutomaticTarget, ClassMethodLocalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    function void g();\n"
      "      int y;\n"
      "      y <= 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "10.4.2"));
}

// A static function's local is static, so writing it with a nonblocking
// assignment is legal.
TEST(NonblockingAutomaticTarget, StaticFunctionLocalElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void fn();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "in nonblocking assignment"), nullptr);
}

// §10.4.2 bars the write whatever part of the automatic variable the target
// names: an element of a block's automatic array, a member of an automatic
// structure, and the elements of a concatenation or a pattern.
TEST(NonblockingAutomaticTarget, SelectMemberAndConcatenationAreErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] f; } nib_t;\n"
      "  initial begin automatic int a[4]; a[0] <= 1; end\n"
      "  task automatic t();\n"
      "    struct packed { logic [3:0] f; } s;\n"
      "    nib_t n;\n"
      "    int x, y;\n"
      "    s.f <= 1;\n"
      "    n.f <= 1;\n"
      "    {x, y} <= 0;\n"
      "    '{x, y} <= '{1, 2};\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 3,
                            "6.21"));
  for (uint32_t line : {8u, 9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "automatic task variable in nonblocking "
                              "assignment",
                              line, "13.3.2"));
  }
}

// A member written through a class or virtual interface handle belongs to the
// object or interface the handle refers to, which outlives the call, and a
// concatenation of module variables writes nothing automatic.
TEST(NonblockingAutomaticTarget, WritesThroughHandlesElaborate) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic sig; endinterface\n"
      "class C; int v; endclass\n"
      "module m;\n"
      "  int m1, m2;\n"
      "  task automatic t();\n"
      "    C c;\n"
      "    virtual ifc vi;\n"
      "    int z;\n"
      "    c.v <= 1;\n"
      "    vi.sig <= 1;\n"
      "    {m1, m2} <= 0;\n"
      "    {>>{z}} <= 32'h1;\n"
      "  endtask\n"
      "endmodule\n",
      f, "m");
  EXPECT_EQ(FindDiag(f, "in nonblocking assignment"), nullptr);
}

// §12.7.1 (printed page 330) declares a loop variable written in a for-loop's
// initialization with automatic lifetime.
TEST(NonblockingAutomaticTarget, ForLoopVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial for (int i = 0; i < 2; i++) i <= 5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 2,
                            "6.21"));
}

// §23.9: a nested block's automatic variable is not what a name outside that
// block reaches, so the module variable of the same name may be written with a
// nonblocking assignment there -- after a begin-end block, a fork-join block
// and a for-loop that each declare one.
TEST(NonblockingAutomaticTarget, OuterVariableOfNestedBlockNameElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x, i;\n"
      "  initial begin\n"
      "    begin automatic int x; x = 1; end\n"
      "    fork automatic int x; join\n"
      "    for (int i = 0; i < 2; i++) x = i;\n"
      "    for (i = 0; i < 2; i++) x = i;\n"
      "    x <= 2;\n"
      "    i <= 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "in nonblocking assignment"), nullptr);
}

// §10.4.2: a nonblocking assignment to an element of a dynamically sized array
// is illegal, and §23.9 decides which array a name reaches: a task's own
// fixed-size array is not the module's queue of the same name.
TEST(NonblockingDynamicElement, LocalFixedArrayShadowingQueueElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  task t(); int q[4]; q[0] <= 1; endtask\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "element of dynamically sized array"), nullptr);
}

// §10.4.2: a class's queue property named in one of its methods is a
// dynamically sized array whose element a nonblocking assignment may not
// write.
TEST(NonblockingDynamicElement, QueuePropertyInClassMethodIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    int q[$];\n"
      "    function void fn(); q[0] <= 1; this.q[1] <= 1; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 4,
      "6.21"));
}

// §10.4.2: an element of a dynamically sized array reached through a class
// handle's property or a structure's member, inline or declared through a
// typedef, is one a nonblocking assignment may not write; a fixed-size member
// is not.
TEST(NonblockingDynamicElement, ElementReachedThroughMemberIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C; int q[$]; endclass\n"
      "  typedef struct { int d[$]; logic [3:0] f; } dq_t;\n"
      "  C h;\n"
      "  struct { int d[]; } s;\n"
      "  dq_t t;\n"
      "  initial begin\n"
      "    h.q[0] <= 1;\n"
      "    s.d[0] <= 1;\n"
      "    t.d[0] <= 1;\n"
      "    t.f[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "nonblocking assignment to element of dynamically sized array", line,
        "6.21"));
  }
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 11,
      "6.21"));
}

// §10.4.2 reaches a dynamically sized dimension wherever it stands among an
// array's unpacked dimensions, the dimensions a typedef wrote included, and a
// concatenation's elements; a select past the unpacked dimensions is a select
// within an element.
TEST(NonblockingDynamicElement, DynamicInnerDimensionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int qt_t[$];\n"
      "  int a[4][$];\n"
      "  int g[2][3];\n"
      "  qt_t qq;\n"
      "  logic [7:0] w, x;\n"
      "  initial begin\n"
      "    a[1][0] <= 1;\n"
      "    qq[0] <= 1;\n"
      "    {x, qq[1]} <= 2;\n"
      "    g[1][0] <= 1;\n"
      "    w[1] <= 1;\n"
      "    {x, w} <= 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "nonblocking assignment to element of dynamically sized array", line,
        "6.21"));
  }
  for (uint32_t line : {11u, 12u, 13u}) {
    EXPECT_FALSE(ReportedError(
        f.diag.Diagnostics(),
        "nonblocking assignment to element of dynamically sized array", line,
        "6.21"));
  }
}

// §7.8: an associative array's index type may be a typedef, and a block may
// declare one.
TEST(NonblockingDynamicElement, LocalTypedefIndexedAssocIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int key_t;\n"
      "  initial begin int aa[key_t]; aa[1] <= 1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 3,
      "6.21"));
}

}  // namespace
