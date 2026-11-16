#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

const char kClassC[] =
    "class C;\n"
    "  rand int x;\n"
    "  int k = 3;\n"
    "  constraint c1 { x == k; }\n"
    "endclass\n";

TEST(ConstraintNameScope, DISABLED_AnInitialBlockLocalLeavesThePropertyRead) {
  const std::string kSrc = std::string(kClassC) +
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    automatic int k = 9;\n"
                           "    automatic C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    got = o.x;\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, AnInitialBlockWithoutTheLocalReadsTheProperty) {
  const std::string kSrc = std::string(kClassC) +
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    automatic C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    got = o.x;\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, DISABLED_ATaskLocalLeavesThePropertyRead) {
  const std::string kSrc = std::string(kClassC) +
                           "module t;\n"
                           "  int got;\n"
                           "  task automatic run();\n"
                           "    int k = 9;\n"
                           "    C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    got = o.x;\n"
                           "  endtask\n"
                           "  initial run();\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, DISABLED_AFunctionLocalLeavesThePropertyRead) {
  const std::string kSrc = std::string(kClassC) +
                           "module t;\n"
                           "  int got;\n"
                           "  function automatic int draw();\n"
                           "    int k = 9;\n"
                           "    C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    return o.x;\n"
                           "  endfunction\n"
                           "  initial got = draw();\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope,
     DISABLED_ACallersHandleLocalLeavesTheGuardedPropertyRead) {
  const std::string kSrc =
      "class H; int v; endclass\n"
      "class G;\n"
      "  rand int y;\n"
      "  H a;\n"
      "  constraint c { if (a != null) y == 1; else y == 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic H a = new;\n"
      "    automatic G g = new;\n"
      "    void'(g.randomize());\n"
      "    got = g.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{2});
}

TEST(ConstraintNameScope, DISABLED_AnInheritedPropertyIsReadPastACallersLocal) {
  const std::string kSrc =
      "class B; int k = 3; endclass\n"
      "class C extends B;\n"
      "  rand int x;\n"
      "  constraint c1 { x == k; }\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic int k = 9;\n"
      "    automatic C o = new;\n"
      "    void'(o.randomize());\n"
      "    got = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, DISABLED_AStaticPropertyIsReadPastACallersLocal) {
  const std::string kSrc =
      "class C;\n"
      "  rand int x;\n"
      "  static int k = 3;\n"
      "  constraint c1 { x == k; }\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic int k = 9;\n"
      "    automatic C o = new;\n"
      "    void'(o.randomize());\n"
      "    got = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, AModuleVariableOfThePropertysNameIsNotRead) {
  const std::string kSrc = std::string(kClassC) +
                           "module t;\n"
                           "  int got;\n"
                           "  int k = 9;\n"
                           "  initial begin\n"
                           "    automatic C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    got = o.x;\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, APackageVariableOfThePropertysNameIsNotRead) {
  const std::string kSrc = std::string(kClassC) +
                           "package p; int k = 9; endpackage\n"
                           "module t;\n"
                           "  import p::*;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    automatic C o = new;\n"
                           "    got = k;\n"
                           "    void'(o.randomize());\n"
                           "    got = o.x;\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, AnotherClassPropertyOfTheNameIsNotRead) {
  const std::string kSrc = std::string(kClassC) +
                           "class D;\n"
                           "  int k = 9;\n"
                           "  function int draw();\n"
                           "    C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    return o.x;\n"
                           "  endfunction\n"
                           "endclass\n"
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    automatic D d = new;\n"
                           "    got = d.draw();\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, DISABLED_AnotherClassMethodLocalOfTheNameIsNotRead) {
  const std::string kSrc = std::string(kClassC) +
                           "class D;\n"
                           "  function int draw();\n"
                           "    int k = 9;\n"
                           "    C o = new;\n"
                           "    void'(o.randomize());\n"
                           "    return o.x;\n"
                           "  endfunction\n"
                           "endclass\n"
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    automatic D d = new;\n"
                           "    got = d.draw();\n"
                           "  end\n"
                           "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, DISABLED_AnOwnMethodLocalOfTheNameIsNotRead) {
  const std::string kSrc =
      "class C;\n"
      "  rand int x;\n"
      "  int k = 3;\n"
      "  constraint c1 { x == k; }\n"
      "  function int draw();\n"
      "    int k = 9;\n"
      "    void'(randomize());\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic C o = new;\n"
      "    got = o.draw();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope,
     DISABLED_AnExternalBlockReadsThePropertyPastACallersLocal) {
  const std::string kSrc =
      "class C;\n"
      "  rand int x;\n"
      "  int k = 3;\n"
      "  extern constraint c1;\n"
      "endclass\n"
      "constraint C::c1 { x == k; }\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic int k = 9;\n"
      "    automatic C o = new;\n"
      "    void'(o.randomize());\n"
      "    got = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope,
     DISABLED_AnInlineBlockReadsThePropertyBeforeTheLocal) {
  const std::string kSrc =
      "class C;\n"
      "  rand int x;\n"
      "  int k = 3;\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic int k = 9;\n"
      "    automatic C o = new;\n"
      "    void'(o.randomize() with { x == k; });\n"
      "    got = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{3});
}

TEST(ConstraintNameScope, AnInlineBlocksLocalQualifierReadsTheCallersName) {
  const std::string kSrc =
      "class C;\n"
      "  rand int x;\n"
      "  int k = 3;\n"
      "endclass\n"
      "module t;\n"
      "  int got;\n"
      "  initial begin\n"
      "    automatic int k = 9;\n"
      "    automatic C o = new;\n"
      "    void'(o.randomize() with { x == local::k; });\n"
      "    got = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), uint64_t{9});
}

}  // namespace
