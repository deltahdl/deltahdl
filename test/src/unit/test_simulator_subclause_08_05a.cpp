#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ObjectPropertySim, UndefinedPropertyReturnsZero) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->GetProperty("nonexistent", f.arena).ToUint64(), 0u);
}

TEST(ObjectPropertySim, PropertyOverwrite) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 10));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 10u);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 20u);
}

TEST(ObjectPropertySim, PropertyReadViaInstance) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.command = 42;\n"
                      "    result = p.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ObjectPropertySim, MultiplePropertyReadWrite) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int header;\n"
                      "  int payload;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.header = 10;\n"
                      "    p.payload = 20;\n"
                      "    result = p.header + p.payload;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            30u);
}

TEST(ObjectPropertySim, EnumAccessViaInstance) {
  EXPECT_EQ(
      RunAndGet(
          "class Packet;\n"
          "  typedef enum integer {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} "
          "PCKT_TYPE;\n"
          "endclass\n"
          "module t;\n"
          "  int result;\n"
          "  initial begin\n"
          "    Packet p;\n"
          "    p = new;\n"
          "    result = p.ERR_OVERFLOW;\n"
          "  end\n"
          "endmodule\n",
          "result"),
      10u);
}

TEST(ObjectPropertySim, ParameterValueAccessViaInstance) {
  EXPECT_EQ(RunAndGet("class vector #(parameter width = 7);\n"
                      "  bit [width:0] data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    vector #(3) v;\n"
                      "    v = new;\n"
                      "    result = v.width;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ObjectPropertySim, ParameterDefaultValueAccessViaInstance) {
  EXPECT_EQ(RunAndGet("class vector #(parameter width = 7);\n"
                      "  bit [width:0] data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    vector v;\n"
                      "    v = new;\n"
                      "    result = v.width;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(ObjectPropertySim,
     ParameterOfAModuleScopeSpecializationConstructedLaterReadViaInstance) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class test_cls #(parameter a = 12);\n"
                      "  endclass\n"
                      "  test_cls #(34) test_obj;\n"
                      "  test_cls dflt;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    test_obj = new;\n"
                      "    dflt = new;\n"
                      "    out = test_obj.a * 100 + dflt.a;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3412u);
}

TEST(ObjectPropertySim, NoRestrictionOnPropertyDataType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  bit [7:0] b;\n"
                      "  logic [15:0] l;\n"
                      "  integer ig;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.b = 8'hAB;\n"
                      "    c.l = 16'hCDEF;\n"
                      "    c.ig = 5;\n"
                      "    result = c.ig;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(ObjectPropertySim, RealPropertyValueRoundTrips) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("class C;\n"
                                 "  real r;\n"
                                 "endclass\n"
                                 "module t;\n"
                                 "  real out;\n"
                                 "  initial begin\n"
                                 "    C c;\n"
                                 "    c = new;\n"
                                 "    c.r = 3.5;\n"
                                 "    out = c.r;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "out"),
                   3.5);
}

TEST(ObjectPropertySim, StringPropertyValueRoundTrips) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  string s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.s = \"hi\";\n"
                      "    out = (c.s == \"hi\") ? 100 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            100u);
}

TEST(ObjectPropertySim, StructPropertyValueRoundTrips) {
  EXPECT_EQ(RunAndGet("typedef struct packed { int x; } pt;\n"
                      "class C;\n"
                      "  pt p;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.p.x = 9;\n"
                      "    out = c.p.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            9u);
}

TEST(ObjectPropertySim, ClassHandlePropertyValueRoundTrips) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int v;\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner in;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    Outer o;\n"
                      "    o = new;\n"
                      "    o.in = new;\n"
                      "    o.in.v = 7;\n"
                      "    out = o.in.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            7u);
}

TEST(ObjectPropertySim, LocalParameterAccessedViaInstance) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  localparam int L = 42;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    out = c.L;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            42u);
}

TEST(ObjectPropertySim, NarrowPropertyTruncatesAValueWrittenFromAMethod) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  bit [3:0] command;\n"
                      "  task clean();\n"
                      "    command = 8'hFF;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.clean();\n"
                      "    result = p.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, TwoStatePropertyZeroesXzWrittenFromAMethod) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class Packet;\n"
      "  bit [4:0] initiator_id;\n"
      "  task clean();\n"
      "    initiator_id = 5'bx;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  logic [4:0] result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.clean();\n"
      "    result = p.initiator_id;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ObjectPropertySim, InheritedPropertyTruncatesAValueWrittenFromAMethod) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  bit [3:0] command;\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  task clean();\n"
                      "    command = 8'hFF;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.clean();\n"
                      "    result = d.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, RealPropertyConvertsAnIntegerWrittenFromAMethod) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("class C;\n"
                                 "  real r;\n"
                                 "  task set();\n"
                                 "    r = 5;\n"
                                 "  endtask\n"
                                 "endclass\n"
                                 "module t;\n"
                                 "  real out;\n"
                                 "  initial begin\n"
                                 "    C c;\n"
                                 "    c = new;\n"
                                 "    c.set();\n"
                                 "    out = c.r;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "out"),
                   5.0);
}

TEST(ObjectPropertySim, NarrowPropertyTruncatesAValueWrittenThroughAHandle) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  bit [3:0] command;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.command = 8'hFF;\n"
                      "    result = p.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, NarrowPropertyTruncatesAValueWrittenThroughSuper) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  bit [3:0] command;\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  task put();\n"
                      "    super.command = 8'hFF;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.put();\n"
                      "    result = d.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, NarrowStaticPropertyTruncatesAValueWrittenByClassName) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static bit [3:0] command;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::command = 8'hFF;\n"
                      "    result = C::command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, NarrowPropertyTruncatesItsDeclarationInitializer) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  bit [3:0] command = 8'hFF;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ObjectPropertySim, UnsignedPropertyDoesNotKeepASignedLiteralsSign) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  bit [7:0] v;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.v = 240;\n"
                      "    result = c.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            240u);
}

TEST(ObjectPropertySim, ThisWriteLeavesTheXBitsOfWhatItRead) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  logic [3:0] mark;\n"
      "  bit [3:0] p;\n"
      "  function void grab();\n"
      "    this.p = mark;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [3:0] kept;\n"
      "  int taken;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.mark = 4'bx1z0;\n"
      "    c.grab();\n"
      "    kept = c.mark;\n"
      "    taken = c.p;\n"
      "  end\n"
      "endmodule\n",
      f, "kept");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "x1z0");
  auto* taken = f.ctx.FindVariable("taken");
  ASSERT_NE(taken, nullptr);
  EXPECT_EQ(taken->value.ToUint64(), 4u);
}

TEST(ObjectPropertySim, SuperWriteLeavesTheXBitsOfWhatItRead) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class Base;\n"
      "  logic [7:0] mark;\n"
      "  bit [7:0] slot;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  task stash();\n"
      "    super.slot = mark;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] kept;\n"
      "  int held;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.mark = 8'hz3;\n"
      "    d.stash();\n"
      "    kept = d.mark;\n"
      "    held = d.slot;\n"
      "  end\n"
      "endmodule\n",
      f, "kept");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "zzzz0011");
  auto* held = f.ctx.FindVariable("held");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 3u);
}

TEST(ObjectPropertySim, AssociativePropertyBelongsToTheObjectAMethodWroteIt) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int aa[int];\n"
                      "  function void put(int k);\n"
                      "    aa[k] = k * 2;\n"
                      "  endfunction\n"
                      "  function int count();\n"
                      "    return aa.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C a = new;\n"
                      "    static C b = new;\n"
                      "    a.put(1);\n"
                      "    a.put(2);\n"
                      "    a.put(3);\n"
                      "    b.put(9);\n"
                      "    out = a.count() * 10 + b.count();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            31u);
}

TEST(ObjectPropertySim, AssociativePropertyIsCopiedByAShallowCopy) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int aa[int];\n"
                      "  function void put(int k);\n"
                      "    aa[k] = k;\n"
                      "  endfunction\n"
                      "  function int count();\n"
                      "    return aa.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C o = new;\n"
                      "    C c;\n"
                      "    o.put(1);\n"
                      "    o.put(2);\n"
                      "    c = new o;\n"
                      "    c.put(3);\n"
                      "    out = o.count() * 10 + c.count();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            23u);
}

TEST(ObjectPropertySim, AssociativePropertyElementReadThroughAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int aa[int];\n"
                      "  function void put(int k, int v);\n"
                      "    aa[k] = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.put(3, 5);\n"
                      "    c.put(4, 9);\n"
                      "    out = c.aa[3] * 10 + c.aa[4];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            59u);
}

TEST(ObjectPropertySim, AssociativePropertyElementWrittenThroughAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int aa[int];\n"
                      "  function int get(int k);\n"
                      "    return aa[k];\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.aa[3] = 71;\n"
                      "    out = c.get(3);\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            71u);
}

TEST(ObjectPropertySim, QueuePropertyPushedInAMethodReadThroughTheHandle) {
  EXPECT_EQ(RunAndGet("class Bag;\n"
                      "  int q[$];\n"
                      "  function void add(int x);\n"
                      "    q.push_back(x);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Bag b = new;\n"
                      "    b.add(11);\n"
                      "    b.add(21);\n"
                      "    b.add(31);\n"
                      "    out = b.q.size() * 1000 + b.q[1] * 10 + b.q[$];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3241u);
}

TEST(ObjectPropertySim, QueuePropertyPushedThroughTheHandleReadInAMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "  function int first();\n"
                      "    return q[0];\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.q.push_back(8);\n"
                      "    c.q.push_back(9);\n"
                      "    out = c.q.size() * 1000 + c.first() * 100;\n"
                      "    void'(c.q.pop_front());\n"
                      "    out = out + c.q.size() * 10 + c.first();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2819u);
}

TEST(ObjectPropertySim, QueuePropertyPopBackAndPopFrontInMethods) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "  function void fill();\n"
                      "    q.push_back(4);\n"
                      "    q.push_back(5);\n"
                      "    q.push_back(6);\n"
                      "  endfunction\n"
                      "  function int take_back();\n"
                      "    return q.pop_back();\n"
                      "  endfunction\n"
                      "  function int take_front();\n"
                      "    return q.pop_front();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.fill();\n"
                      "    out = c.take_back() * 100 + c.take_front() * 10;\n"
                      "    out = out + c.q.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            641u);
}

TEST(ObjectPropertySim, QueueOfHandlesPropertyElementMember) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v;\n"
                      "  function new(int x);\n"
                      "    v = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Bag;\n"
                      "  Item q[$];\n"
                      "  function void add(int x);\n"
                      "    Item it = new(x);\n"
                      "    q.push_back(it);\n"
                      "  endfunction\n"
                      "  function int total();\n"
                      "    int s = 0;\n"
                      "    foreach (q[i]) s += q[i].v;\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Bag b = new;\n"
                      "    b.add(11);\n"
                      "    b.add(21);\n"
                      "    b.add(31);\n"
                      "    out = (b.q.size() * 100 + b.q[1].v) * 100;\n"
                      "    out = (out + b.total()) * 100 + b.q[$].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3216331u);
}

TEST(ObjectPropertySim, QueuePropertyElementWrittenByIndex) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "  function void fill();\n"
                      "    q.push_back(1);\n"
                      "    q.push_back(2);\n"
                      "  endfunction\n"
                      "  function void set_second(int x);\n"
                      "    q[1] = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.fill();\n"
                      "    c.q[0] = 9;\n"
                      "    c.set_second(8);\n"
                      "    out = c.q[0] * 10 + c.q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            98u);
}

TEST(ObjectPropertySim,
     HandleArrayPropertyElementConstructedAndReadFromModule) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  function new(int x);\n"
                      "    v = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Tree;\n"
                      "  Node kids[2];\n"
                      "  function new();\n"
                      "    kids[0] = new(20);\n"
                      "    kids[1] = new(21);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Tree tr = new;\n"
                      "    out = tr.kids[1].v * 100 + tr.kids[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2120u);
}

TEST(ObjectPropertySim, HandleArrayPropertyElementMemberReadInAMethod) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  function new(int x);\n"
                      "    v = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Tree;\n"
                      "  Node kids[2];\n"
                      "  function new();\n"
                      "    kids[0] = new(7);\n"
                      "    kids[1] = new(9);\n"
                      "  endfunction\n"
                      "  function int first();\n"
                      "    return kids[0].v;\n"
                      "  endfunction\n"
                      "  function int second();\n"
                      "    return kids[1].v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Tree tr = new;\n"
                      "    out = tr.first() * 10 + tr.second();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            79u);
}

TEST(ObjectPropertySim, HandleArrayPropertyNonNullElementsCountedInAMethod) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  function new(int x);\n"
                      "    v = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Tree;\n"
                      "  Node kids[3];\n"
                      "  function new();\n"
                      "    kids[0] = new(1);\n"
                      "    kids[2] = new(3);\n"
                      "  endfunction\n"
                      "  function int count();\n"
                      "    int n = 0;\n"
                      "    for (int i = 0; i < 3; i++)\n"
                      "      if (kids[i] != null) n++;\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Tree tr = new;\n"
                      "    out = tr.count();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

}  // namespace
