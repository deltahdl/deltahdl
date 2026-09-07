#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PassByValueSim, DefaultMechanismWithoutDirectionQualifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function int add_ten(int v);\n"
      "    v = v + 10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    y = add_ten(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 15u}});
}

TEST(PassByValueSim, AutomaticFunctionRetainsLocalCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function automatic int modify_arg(input int v);\n"
      "    v = v + 100;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    y = modify_arg(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, TaskInputArgNotVisibleOutside) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task modify(input int v);\n"
      "    v = v + 100;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    modify(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

// C1 in the task syntactic position: a task argument written with no direction
// qualifier defaults to input and is therefore passed by value. The callee
// mutates its local copy, yet the caller's variable is unchanged (x stays 4),
// while the copied-in value reaches the callee (y == 54). Distinct from the
// function no-qualifier case and from the explicit-input task case.
TEST(PassByValueSim, TaskDefaultDirectionArgPassedByValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task apply(int v);\n"
      "    v = v + 50;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 4;\n"
      "    apply(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 4u}, {"y", 54u}});
}

TEST(PassByValueSim, MultipleArgsCopiedIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  function int swap_and_add(int x, int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 7;\n"
      "    result = swap_and_add(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}, {"result", 10u}});
}

TEST(PassByValueSim, RecursiveAutomaticUsesPerActivationStackCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  function automatic int sum_down(int n);\n"
      "    if (n == 0) return 0;\n"
      "    return n + sum_down(n - 1);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = sum_down(4);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 10u}});
}

TEST(PassByValueSim, SameSourceBoundToTwoFormalsCopiesIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  function int scale_first_minus_second(int a, int b);\n"
      "    a = a * 10;\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    result = scale_first_minus_second(x, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"result", 63u}});
}

// §13.5.1 illustrates the copy with an unpacked array formal (byte packet[]).
// Passing an array by value copies every element into the subroutine area: the
// callee reads the copied-in values (sum == 7) yet its later writes to the
// local copy leave the caller's array untouched, so the mutation is not visible
// outside the call.
TEST(PassByValueSim, UnpackedArrayArgumentCopiedElementwise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte packet [0:1];\n"
      "  int total;\n"
      "  function int sum_then_clobber(byte p [0:1]);\n"
      "    int s;\n"
      "    s = p[0] + p[1];\n"
      "    p[0] = 99;\n"
      "    p[1] = 99;\n"
      "    return s;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    packet[0] = 3;\n"
      "    packet[1] = 4;\n"
      "    total = sum_then_clobber(packet);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"packet[0]", 3u}, {"packet[1]", 4u}, {"total", 7u}});
}

// §13.5.1 copies each argument into the subroutine area, and §10.8 lists "the
// passing of a value to a subroutine input, output, or inout argument" among
// the assignment-like contexts, so §10.7 truncates or extends the actual into
// the width the formal's type declares. §6.18 makes a formal written with a
// user-defined type name an object of the type that name stands for, which is
// the width in question here.
//
// Each case passes a value the formal's type is too narrow to hold, because
// that is what the two answers disagree about: a formal the simulator could not
// size was left at whatever width the caller's expression had, so `8'hFF` read
// 255 where four bits read 15. A formal of exactly 32 bits, or a value that
// fits the type, reads the same either way.
TEST(PassByValueSim, TypedefNameInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  function int take(input nib p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(8'hFF);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

// A task's formals are bound by the same code as a function's, but a task is
// reached by its own call path and neither case stands for the other. The
// output formal here is how the value is read back and is a 32-bit `int`, so
// what it reports is the input formal's width and not its own.
TEST(PassByValueSim, TypedefNameTaskInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  task take(input nib p, output int o);\n"
      "    o = p;\n"
      "  endtask\n"
      "  initial begin\n"
      "    y = 0;\n"
      "    take(8'hFF, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

// The four-bit cases cannot say a formal wider than the 32 bits an unsized
// formal used to fall back to keeps its own width: a clamp to 32 would truncate
// 8'hFF to 15 as well. Forty bits spans two words, and the three answers
// separate -- 48'hFFFF00000001 passed whole reads 281470681743361, clamped to
// thirty-two reads 1, and truncated to the forty bits `wide` declares reads
// 1095216660481, whose set bits above the first word are what say the high word
// survived.
TEST(PassByValueSim, TypedefNameFormalWiderThanOneWordKeepsItsHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] y;\n"
      "  function logic [63:0] take(input wide p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(48'hFFFF00000001);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 1095216660481ull}});
}

// §8.3 makes a class variable a handle to an object rather than an object of a
// width, so there is nothing here for §10.7 to truncate and the formal takes
// the handle it was passed. What makes this worth a case of its own is that a
// class name can reach the elaborated typedef table and answer a width there:
// §8.27's forward declaration records the name before the class exists, with a
// data type that is still DataTypeKind::kImplicit, which §6.10 makes a scalar.
// A formal sized from that answer would hold one bit of the handle and read 0
// rather than the 42 the object carries -- and only in a design that happens to
// forward- declare the class, which is why the accompanying `typedef class
// Packet;` is the whole point of the case and not decoration.
TEST(PassByValueSim, ForwardDeclaredClassFormalKeepsTheWholeHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class Packet;\n"
      "class Packet;\n"
      "  integer i = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int y;\n"
      "  function integer read_i(Packet p);\n"
      "    read_i = p.i;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    Packet q;\n"
      "    q = new;\n"
      "    y = read_i(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 42u}});
}

}  // namespace
