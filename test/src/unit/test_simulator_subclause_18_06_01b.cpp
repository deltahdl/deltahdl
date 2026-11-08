#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kPackets =
    "class Packet;\n"
    "  rand bit [7:0] kind;\n"
    "  rand bit [7:0] size;\n"
    "  constraint bounded { size < 64; }\n"
    "endclass\n"
    "class Framed extends Packet;\n"
    "  constraint even { size[0] == 0; }\n"
    "endclass\n"
    "class Oversized extends Packet;\n"
    "  constraint oversize { size > 100; }\n"
    "endclass\n";

TEST(RandomizeMethodRun, TheVirtualMethodRandomizesTheObjectsOwnClass) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "module t;\n"
                     "  int success = 0, held = 0, evens = 0;\n"
                     "  initial begin\n"
                     "    static Framed fr = new;\n"
                     "    static Packet handle = fr;\n"
                     "    repeat (32) begin\n"
                     "      if (handle.randomize()) success++;\n"
                     "      if (fr.size < 64) held++;\n"
                     "      if (fr.size[0] == 0) evens++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d %0d\", success, held, evens);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 32 32\n");
}

TEST(RandomizeMethodRun, ADerivedClassCanRenderTheConstraintsUnsatisfiable) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "module t;\n"
                     "  int success;\n"
                     "  initial begin\n"
                     "    static Oversized ov = new;\n"
                     "    ov.size = 5;\n"
                     "    success = ov.randomize();\n"
                     "    $display(\"%0d %0d\", success, ov.size);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "0 5\n");
}

TEST(RandomizeMethodRun, AnyHandleExpressionNamesTheObjectRandomized) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "class Holder;\n"
                     "  Packet inner;\n"
                     "  function new(); inner = new; endfunction\n"
                     "endclass\n"
                     "module t;\n"
                     "  Packet arr[2];\n"
                     "  Holder h;\n"
                     "  Packet made;\n"
                     "  function automatic Packet make();\n"
                     "    made = new;\n"
                     "    made.size = 200;\n"
                     "    return made;\n"
                     "  endfunction\n"
                     "  int r1, r2, r3;\n"
                     "  initial begin\n"
                     "    arr[1] = new;\n"
                     "    arr[1].size = 200;\n"
                     "    h = new;\n"
                     "    h.inner.size = 200;\n"
                     "    r1 = arr[1].randomize();\n"
                     "    r2 = h.inner.randomize();\n"
                     "    r3 = make().randomize();\n"
                     "    $display(\"%0d %0d %0d %0d %0d %0d\", r1, r2, r3,\n"
                     "             arr[1].size < 64, h.inner.size < 64,\n"
                     "             made.size < 64);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 1 1 1 1 1\n");
}

TEST(RandomizeMethodRun, AnyHandleExpressionTakesAnInlineConstraint) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "class Holder;\n"
                     "  Packet inner;\n"
                     "  function new(); inner = new; endfunction\n"
                     "endclass\n"
                     "module t;\n"
                     "  Packet arr[1];\n"
                     "  Holder h;\n"
                     "  int r1, r2;\n"
                     "  initial begin\n"
                     "    arr[0] = new;\n"
                     "    h = new;\n"
                     "    r1 = arr[0].randomize() with { size == 7; };\n"
                     "    r2 = h.inner.randomize() with { size == 9; };\n"
                     "    $display(\"%0d %0d %0d %0d\", r1, r2, arr[0].size,\n"
                     "             h.inner.size);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 1 7 9\n");
}

TEST(RandomizeMethodRun, ANullHandleExpressionIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kPackets) +
                                  "module t;\n"
                                  "  Packet arr[1];\n"
                                  "  int r = 5;\n"
                                  "  initial r = arr[0].randomize();\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'randomize' called through a null handle",
                            15, "8.4"));
}

TEST(RandomizeMethodRun, ACallWrittenWithoutItsListRandomizes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    rand bit [3:0] x;\n"
      "    constraint c { x == 4'd9; }\n"
      "    function int again(); return randomize; endfunction\n"
      "  endclass\n"
      "  typedef struct { int randomize; } s_t;\n"
      "  C h = new;\n"
      "  s_t s;\n"
      "  s_t sa [2];\n"
      "  int ok1, ok2, field, element;\n"
      "  initial begin\n"
      "    s.randomize = 6;\n"
      "    sa[1].randomize = 4;\n"
      "    ok1 = h.randomize;\n"
      "    h.x = 0;\n"
      "    ok2 = h.again();\n"
      "    field = s.randomize;\n"
      "    element = sa[1].randomize;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", ok1, ok2, h.x, field, element);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 9 6 4\n");
}

}  // namespace
