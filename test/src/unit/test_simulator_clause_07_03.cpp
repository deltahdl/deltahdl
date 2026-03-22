#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.3: Union is single storage — write one member, read same member back.
TEST(UnionSimulation, UnpackedUnionMemberWriteReadBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int i; int j; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.i = 42;\n"
      "    result = u.i;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.3: Union is single storage — write via one member, read via another.
TEST(UnionSimulation, UnpackedUnionSingleStorage_CrossMemberRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int a; int b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 99;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

// §7.3: Uninitialized unpacked union defaults to first member's type default.
// First member is int (2-state) → default is 0.
TEST(UnionSimulation, UnpackedUnionDefaultInit_IntFirstMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int i; logic [31:0] l; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = u.i;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// §7.3: Overwrite union member and read back whole-variable value.
TEST(UnionSimulation, UnpackedUnionOverwrite) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int a; int b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 10;\n"
      "    u.b = 20;\n"
      "    result = u.a;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

}  // namespace
