#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
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

}  // namespace
