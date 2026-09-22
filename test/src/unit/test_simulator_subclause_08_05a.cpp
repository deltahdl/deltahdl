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

// §8.5 (printed page 179) with §8.25: a parameter is read through a handle
// as a property is, and the handle declared at module scope with a
// specialization, `test_cls #(34) test_obj;` on a class the module itself
// declares, constructed later by `test_obj = new`, reads the 34 the
// specialization gave it, while a handle declared with no `#(...)` reads
// the default 12: 3412. This is the suite's 8.5--parameters.sv (#2916),
// which run 30725357212 reported reading 12; e87e650bc binds the
// specialization's actuals on the object at that later construction, and
// the two cases above hold the handle in the initial and construct it
// there.
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

// §8.5: a class property may have any data type. Exercising the non-integral
// data-type forms end to end - a real property survives an instance-qualified
// write and read.
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

// §8.5: a string-typed class property holds and returns its value.
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

// §8.5: a class property may be an aggregate (packed struct) type; the nested
// member is reachable through the instance.
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

// §8.5: a class property may itself be a class handle; the nested object's
// property is reachable through the outer instance.
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

// §8.5: a local value parameter (localparam) of a class can be read by
// qualifying its name with an instance handle, just like a value parameter.
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

// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so an assignment to a property from a method is one and
// §10.7 truncates or extends it into the object the declaration made. §8.2's
// own Packet is the case: it declares `bit [3:0] command;` beside a `clean`
// task that assigns to it, and to `initiator_id` the `5'bx` §6.11.2 gives a
// `bit` no room for. The property took the value's width instead, so both
// survived.

// The width. Eight bits of 8'hFF into the four `command` declares reads 15;
// the property carrying the literal's own width reads 255.
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

// The state-ness, written as §8.2 writes it. The value is carried out into a
// 4-state variable and read through IsKnown, because an x reads as zero through
// ToUint64 either way -- what separates the two answers is whether the bits are
// known, not what they add up to.
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

// A property declared on a base class is not in the derived type's own list, so
// the width has to be looked for along the chain SetPropertyForType walks to
// find the storage. A method of the derived class writing the base's property
// is what asks for that: a lookup that stopped at the method's own class would
// find nothing and write the value whole.
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

// §6.12.1 converts a value crossing the real/integer boundary rather than
// reinterpreting its bits, so a real property assigned an integer holds the
// double. RealPropertyValueRoundTrips above writes the property from outside
// the class, which is a different writer; this one writes it from a method,
// where the §10.7 resize a property write now performs would otherwise store
// the integer's bit pattern and drop the flag the read needs -- 5 read back as
// a double that way is 2.5e-323 rather than 5.0.
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

// §10.4 names the same left-hand sides for a procedural assignment wherever it
// is written, so which spelling reaches a property cannot decide what the
// property holds. The method-side write truncates; these are its siblings.

// Through a handle, which is the writer most designs use.
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

// §8.15's `super.x` names the parent slice, so the width is the one the parent
// declared. This write reaches the storage by its own arm rather than through
// the one the unqualified name takes.
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

// §8.9's static property, written by its class name. Its width is recorded the
// same way and was consulted no more than the others'.
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

// §6.8 executes a declaration's initializer as an assignment to the declared
// object, so a property's default is coerced into it as a later write is. The
// no-initializer arm beside it already sized from the declared width, which is
// what made this one's silence visible.
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

// §6.11.3 gives `bit` no sign, so a value that arrived signed does not stay
// signed once it is in the property. A property is only its Logic4Vec -- unlike
// a variable, which keeps the flag beside the value and is read through it --
// so the declaration's signedness has to be imposed as the value is written.
// The unsized decimal 240 is a signed literal, and truncated into eight bits
// while still marked signed it reads back as -16.
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

// A guard rather than a discriminating case: it holds today and is meant to go
// on holding. §6.8 makes the property and what was read into it two storage
// elements, and what keeps them apart is a copy taken where a subroutine body
// produces its right-hand value (OwnRhsWords in ExecFuncBlockingAssign,
// eval_function_body.cpp), not anything the property write itself does. Every
// write a method makes passes that one point, so the 2-state coercion behind
// `this.p` has a buffer of its own to clear.
//
// `mark` is 4-state and `p` is `bit` at the same width: the pair that shares a
// buffer if the copy is ever dropped, since a 4-state target coerces nothing
// and an unequal width allocates. 4'bx1z0 carries an x and a z, so either kind
// of unknown would show; ToUint64 would show neither, projecting both to 0.
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

// The same guard for §8.15's `super.slot`, which reaches the parent's storage
// by an arm of its own instead of the one the unqualified name takes, and so
// asks for the coercion itself. It draws its value from the same production
// point as the write above, so the copy taken there covers this arm too; the
// case stands here so a later change to this arm alone cannot quietly stop
// being covered. 8'hz3 is four z bits over 0011, and `slot` is `bit` at the
// width the parent declared -- again the pair that would share a buffer.
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

// §8.5 puts no restriction on a property's data type, so a property declared
// with an associative dimension (§7.8) is an associative array of the object:
// an element written in a method by the property's bare name is an entry of
// that object's array, and a second object of the class holds none of them.
// The write went nowhere before the object held such an array, so both counts
// read 0.
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
                      "    C a = new;\n"
                      "    C b = new;\n"
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

// §8.12: a shallow copy, `C c = new o`, copies the object's properties, the
// associative one among them, so the copy starts with the source's entries and
// an entry written to the copy afterwards is the copy's alone.
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
                      "    C o = new;\n"
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

// §8.5: an element of the associative property is read through the instance
// as any property is, `o.aa[k]`, and what it reads is the entry a method of
// the object wrote. The read fell to a bit-select of the property's scalar
// carrier before, answering 0.
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
                      "    C c = new;\n"
                      "    c.put(3, 5);\n"
                      "    c.put(4, 9);\n"
                      "    out = c.aa[3] * 10 + c.aa[4];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            59u);
}

// §8.5 the other way round: an element written through the instance from the
// module is the entry a method of the object reads by the property's bare
// name (§8.11).
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
                      "    C c = new;\n"
                      "    c.aa[3] = 71;\n"
                      "    out = c.get(3);\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            71u);
}

// §8.5 with §7.10: a property declared with a queue dimension is a queue of
// the object. Three push_back calls in a method grow it to three elements,
// which the module reads through the handle: size() as 3, the second element
// and, §7.10 naming the last element `$`, the last.
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
                      "    Bag b = new;\n"
                      "    b.add(11);\n"
                      "    b.add(21);\n"
                      "    b.add(31);\n"
                      "    out = b.q.size() * 1000 + b.q[1] * 10 + b.q[$];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3241u);
}

// §8.5 the other way round: elements pushed through the handle from the
// module are what a method reads by the property's bare name (§8.11), and a
// pop_front through the handle removes the first of them.
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
                      "    C c = new;\n"
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

// §7.10.2.6 and §7.10.2.7: pop_back and pop_front on a queue property answer
// the last and the first element and remove them, leaving the middle one.
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
                      "    C c = new;\n"
                      "    c.fill();\n"
                      "    out = c.take_back() * 100 + c.take_front() * 10;\n"
                      "    out = out + c.q.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            641u);
}

// §8.5 with §8.4: a queue property of a class type holds handles, so a member
// select on an element, `b.q[1].v` through the handle and `q[i].v` in a
// method's foreach (§12.7.3), reads the property of the object the element
// refers to. Size 3, second element 21, total 63 and last 31.
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
                      "    Bag b = new;\n"
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

// §7.10.1: an element of a queue property is written by index, through the
// handle from the module and by the bare name in a method (§8.11), and each
// write lands on the object's queue.
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
                      "    C c = new;\n"
                      "    c.fill();\n"
                      "    c.q[0] = 9;\n"
                      "    c.set_second(8);\n"
                      "    out = c.q[0] * 10 + c.q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            98u);
}

// §7.4.2 makes an unpacked array of any data type and §8.5 puts no restriction
// on a property's type, so `Node kids[2]` holds two handles (§8.4); `kids[0] =
// new(20)` in the constructor constructs a Node into the element, and
// `tr.kids[1].v` from the module reads through the handle it holds.
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
                      "    Tree tr = new;\n"
                      "    out = tr.kids[1].v * 100 + tr.kids[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2120u);
}

// §8.11: the bare `kids[0].v` in a method of the class reads the property of
// the object the element of the running method's own array property holds.
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
                      "    Tree tr = new;\n"
                      "    out = tr.first() * 10 + tr.second();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            79u);
}

// §8.4: an element the constructor never wrote is the null handle, so a for
// loop over the indices counting `kids[i] != null` counts the constructed
// elements alone -- two of three, where a count of every element gives 3 and
// elements holding no object give 0.
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
                      "    Tree tr = new;\n"
                      "    out = tr.count();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

}  // namespace
