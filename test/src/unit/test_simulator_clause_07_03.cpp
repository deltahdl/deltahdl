#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(UnionSimulation, UnpackedUnionDefaultInit_FourStateFirstMemberIsX) {
  // §7.3: a variable of an unpacked union type with no initial value takes the
  // default initial value of the *first member's* type, in declaration order.
  // Here the first member is a 4-state logic vector, so the default is x --
  // distinct from the value a 2-state first member (e.g. int -> 0) would give.
  // This exercises the first-member 4-state rule, not an "any 4-state member"
  // rule: the union also has a 2-state member, yet the default must be x.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { logic [7:0] a; int b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $isunknown(u.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(UnionSimulation, UnpackedUnionCommonInitialSequenceSharedPrefix) {
  // §7.3: when an unpacked union holds several unpacked structures that share a
  // common initial sequence, the common initial part written through one member
  // can be inspected through another. Both structures share `int tag` as their
  // first member; writing it through one struct member and reading it through
  // the other observes the shared union storage aliasing the common prefix.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int tag; int x; } sa_t;\n"
      "  typedef struct { int tag; int y; } sb_t;\n"
      "  typedef union { sa_t a; sb_t b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a.tag = 42;\n"
      "    result = u.b.tag;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
