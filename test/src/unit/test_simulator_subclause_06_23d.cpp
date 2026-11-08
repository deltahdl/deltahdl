#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypeOfThisClassSim, RegistryExampleReturnsHandlesOfTheEnclosingClass) {
  const std::string kSrc =
      "class registry #(type T = int);\n"
      "  int val = 9;\n"
      "  static function type(this) get();\n"
      "    var static type(this) m_inst;\n"
      "    if (m_inst == null) m_inst = new();\n"
      "    return m_inst;\n"
      "  endfunction\n"
      "endclass\n"
      "class my_int_registry extends registry #();\n"
      "  int own = 4;\n"
      "  function type(this) other();\n"
      "    return this;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  registry #(int) r, r2;\n"
      "  my_int_registry m, n, o;\n"
      "  int same, v, w, back;\n"
      "  initial begin\n"
      "    m = new;\n"
      "    m.val = 1;\n"
      "    n = new;\n"
      "    n.val = 2;\n"
      "    n.own = 5;\n"
      "    o = n.other();\n"
      "    r = registry #(int)::get();\n"
      "    r2 = registry #()::get();\n"
      "    same = r == r2;\n"
      "    v = r.val;\n"
      "    w = o.own;\n"
      "    back = o == n;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "same"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "v"), 9u);
  EXPECT_EQ(RunAndGet(kSrc, "w"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "back"), 1u);
}

TEST(TypeOfThisClassSim, DerivedClassIsNotItsBase) {
  const std::string kSrc =
      "class B;\n"
      "  function int in_base();\n"
      "    return type(this) == type(B);\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  function int in_derived();\n"
      "    int r = 0;\n"
      "    if (type(this) == type(D)) r = r | 1;\n"
      "    if (type(this) == type(B)) r = r | 2;\n"
      "    if (type(this) != type(B)) r = r | 4;\n"
      "    return r;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r, s;\n"
      "  D d;\n"
      "  initial begin\n"
      "    d = new;\n"
      "    r = d.in_derived();\n"
      "    s = d.in_base();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b101u);
  EXPECT_EQ(RunAndGet(kSrc, "s"), 1u);
}

TEST(TypeOfThisClassSim, SpecializationMatchesItselfOnly) {
  const std::string kSrc =
      "class registry #(type T = int);\n"
      "  function int check();\n"
      "    int r = 0;\n"
      "    if (type(this) == type(registry #(byte))) r = r | 1;\n"
      "    if (type(this) == type(registry #(int))) r = r | 2;\n"
      "    if (type(this) == type(registry #())) r = r | 4;\n"
      "    if (type(this) == type(registry)) r = r | 8;\n"
      "    return r;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int b, i;\n"
      "  registry #(byte) rb;\n"
      "  registry #(int) ri;\n"
      "  initial begin\n"
      "    rb = new;\n"
      "    ri = new;\n"
      "    b = rb.check();\n"
      "    i = ri.check();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "b"), 0b0001u);
  EXPECT_EQ(RunAndGet(kSrc, "i"), 0b1110u);
}

TEST(TypeOfThisClassSim, PropertyAndFormalHoldHandlesOfTheClass) {
  const std::string kSrc =
      "class node;\n"
      "  int val;\n"
      "  var type(this) next;\n"
      "  function new(int v);\n"
      "    val = v;\n"
      "  endfunction\n"
      "  function int twice();\n"
      "    return 2 * val;\n"
      "  endfunction\n"
      "  function int link(input var type(this) n);\n"
      "    next = n;\n"
      "    return n.twice();\n"
      "  endfunction\n"
      "  function void grow();\n"
      "    next = new(val + 1);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c, d, e, same;\n"
      "  node x, y, z, g;\n"
      "  initial begin\n"
      "    x = new(1);\n"
      "    y = new(2);\n"
      "    z = new(3);\n"
      "    g = new(7);\n"
      "    d = y.link(z);\n"
      "    e = x.link(y);\n"
      "    a = x.next.val;\n"
      "    b = x.next.next.val;\n"
      "    same = x.next == y;\n"
      "    g.grow();\n"
      "    c = g.next.val;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "a"), 2u);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 3u);
  EXPECT_EQ(RunAndGet(kSrc, "same"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "c"), 8u);
  EXPECT_EQ(RunAndGet(kSrc, "d"), 6u);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 4u);
}

TEST(TypeOfThisClassSim, SpecializationPropertyHoldsItsOwnSpecialization) {
  const std::string kSrc =
      "class ring #(int W = 4);\n"
      "  bit [W-1:0] v;\n"
      "  var type(this) next;\n"
      "  function new(bit [W-1:0] x);\n"
      "    v = x;\n"
      "  endfunction\n"
      "  function void grow();\n"
      "    next = new(v + 1);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a;\n"
      "  ring #(12) c, h;\n"
      "  initial begin\n"
      "    c = new(12'h7FE);\n"
      "    c.grow();\n"
      "    h = c.next;\n"
      "    a = h.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "a"), 0x7FFu);
}

TEST(TypeOfThisClassSim, DeclarationThroughThisTakesThePropertysType) {
  const std::string kSrc =
      "class B;\n"
      "  byte x;\n"
      "  logic [3:0] y [2];\n"
      "  function int probe();\n"
      "    var type(this.x) v;\n"
      "    var type(this.y) w;\n"
      "    var type(x) u;\n"
      "    v = -1;\n"
      "    return $bits(v) * 1000 + (v < 0) * 100 + $size(w) * 10 +\n"
      "           $bits(u) / 8;\n"
      "  endfunction\n"
      "endclass\n"
      "class E extends B;\n"
      "  int z;\n"
      "  function int inherited();\n"
      "    var type(this.x) v;\n"
      "    var type(x) u;\n"
      "    var type(this.z) w;\n"
      "    return $bits(v) * 1000 + $bits(u) * 10 + $bits(w) / 32;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int p, i;\n"
      "  E e;\n"
      "  initial begin\n"
      "    e = new;\n"
      "    p = e.probe();\n"
      "    i = e.inherited();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "p"), 8121u);
  EXPECT_EQ(RunAndGet(kSrc, "i"), 8081u);
}

}  // namespace
