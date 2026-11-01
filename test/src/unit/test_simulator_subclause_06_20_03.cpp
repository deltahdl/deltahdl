#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TypeParameterSim, DefaultTypeParamResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter type T = shortint;\n"
      "  T x;\n"
      "  initial x = 32'hFFFFFFFF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(TypeParameterSim, LocalparamTypeResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam type T = byte;\n"
      "  T data;\n"
      "  initial data = 8'hAB;\n"
      "endmodule\n",
      f, "data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §6.20.3: a type parameter whose type is a packed vector sets the width of a
// dependent variable, observable at run time when an over-wide value assigned
// to it is truncated to that width.
TEST(TypeParameterSim, VectorTypeParamResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter type T = logic [7:0];\n"
      "  T x;\n"
      "  initial x = 16'hABCD;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(TypeParameterSim, MultipleTypeParamsResolveCorrectly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type A = int;\n"
      "  parameter type B = shortint;\n"
      "  A x;\n"
      "  B y;\n"
      "  initial begin\n"
      "    x = 32'hDEADBEEF;\n"
      "    y = 16'hCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);

  EXPECT_EQ(vx->value.width, 32u);
  EXPECT_EQ(vx->value.ToUint64(), 0xDEADBEEFu);
  EXPECT_EQ(vy->value.width, 16u);
  EXPECT_EQ(vy->value.ToUint64(), 0xCAFEu);
}

// §23.10.2 with §6.20.3: an override is written in the instantiating module,
// so `child #(bus_t)` hands the child the parent's bus_t, 13 bits, although the
// child's own type parameter has the same name; so does §6.23's
// `parameter type bus_t = type(A_bus)` for a parent's bus_t.
TEST(TypeParameterSim, OverrideNamesTheParentsTypeOfTheSameName) {
  const std::string kSrc =
      "module child #(type bus_t = bit [7:0]) ();\n"
      "  bus_t v;\n"
      "  int w;\n"
      "  initial w = $bits(v);\n"
      "endmodule\n"
      "module t;\n"
      "  bit [12:0] A_bus;\n"
      "  parameter type bus_t = bit [12:0];\n"
      "  parameter type ref_t = type(A_bus);\n"
      "  child #(bus_t) u1 ();\n"
      "  child #(.bus_t(ref_t)) u2 ();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "u1.w"), 13u);
  EXPECT_EQ(RunAndGet(kSrc, "u2.w"), 13u);
}

// Each override reads the parent's names, not a child parameter an earlier
// override has already set: `.A(B), .B(A)` swaps the parent's byte and
// shortint into the child.
TEST(TypeParameterSim, OverridesSwappingTwoNamesReadTheParents) {
  const std::string kSrc =
      "module child #(type A = int, type B = int) ();\n"
      "  A a; B b;\n"
      "  int wa, wb;\n"
      "  initial begin wa = $bits(a); wb = $bits(b); end\n"
      "endmodule\n"
      "module t;\n"
      "  parameter type A = byte;\n"
      "  parameter type B = shortint;\n"
      "  child #(.A(B), .B(A)) u ();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "u.wa"), 16u);
  EXPECT_EQ(RunAndGet(kSrc, "u.wb"), 8u);
}

// A.2.8 admits a parameter_declaration among a begin-end block's items, and
// §6.20.3 has a type parameter name a data type, so `T x` is a `logic [7:0]`
// that keeps eight bits of 9'h1FF, and `U y` a signed shortint holding -1.
// The block's type parameter named no type a declaration was sized by, so
// both fell to the 32-bit carrier of a type nothing sizes.
TEST(TypeParameterSim, BlockTypeParamNamesTheTypeOfALaterDeclaration) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  initial begin\n"
                 "    parameter type T = logic [7:0];\n"
                 "    localparam type U = shortint;\n"
                 "    T x;\n"
                 "    U y;\n"
                 "    x = 9'h1FF;\n"
                 "    y = -1;\n"
                 "    $display(\"%0d %0d %0d %0d\", $bits(x), x, $bits(y),"
                 " y);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "8 255 16 -1\n");
}

// The same rule in a subroutine body, whose block_item_declarations A.2.6 and
// A.2.7 take from A.2.8: a function's `bit [3:0]` local keeps four bits of
// 5'h1F, and a task's `byte` local holds 9'h181 as the signed -127.
TEST(TypeParameterSim, SubroutineTypeParamNamesTheTypeOfALocal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic int f();\n"
                       "    parameter type T = bit [3:0];\n"
                       "    T v;\n"
                       "    v = 5'h1F;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  task automatic tk(output int o);\n"
                       "    localparam type B = byte;\n"
                       "    B b;\n"
                       "    b = 9'h181;\n"
                       "    o = b;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    int r;\n"
                       "    tk(r);\n"
                       "    $display(\"%0d %0d\", f(), r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "15 -127\n");
}

// §6.20.3 with §7.4: a declaration writing unpacked dimensions after a
// block's type parameter is an array of the parameter's type, so each element
// of `P b [2]` is a signed shortint holding -1.
TEST(TypeParameterSim, ArrayOfABlockTypeParamHasElementsOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin\n"
                       "    parameter type P = shortint;\n"
                       "    P b [2];\n"
                       "    b[0] = -1;\n"
                       "    $display(\"%0d %0d\", $bits(b[0]), b[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "16 -1\n");
}

// §6.20.3: the clause's own example, written at compilation-unit scope. P's
// type parameter C is bound to the class X, and C::T selects X's int through it
// in a type parameter assignment, so a P_X object's y is a 32-bit int: a value
// wider than 32 bits keeps only its low 32.
TEST(TypeParameterSim, ClassTypeSelectedThroughTypeParamAssignment) {
  EXPECT_EQ(RunAndGet("class P #(type C);\n"
                      "  localparam type C_t = C::T;\n"
                      "  C_t y;\n"
                      "endclass\n"
                      "class X;\n"
                      "  typedef int T;\n"
                      "endclass\n"
                      "typedef P#(X) P_X;\n"
                      "module t;\n"
                      "  bit [63:0] r;\n"
                      "  P_X o;\n"
                      "  initial begin\n"
                      "    o = new;\n"
                      "    o.y = 40'h12_3456_789A;\n"
                      "    r = {$bits(o.y), o.y};\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            (uint64_t{32} << 32) | 0x3456789Au);
}

// §6.20.3 with §6.18: a class property declared through a name the class gives
// its meaning to is as wide as the type the name reaches -- a typedef of the
// class, a body `localparam type`, a type selected through a type parameter
// bound to a class, under the default specialization and under one naming the
// class, and a compilation-unit typedef or a class's typedef named directly.
// Each reaches byte, so a 40-bit value written to y keeps its low 8 bits, and
// r holds the 32-bit $bits(o.y) above those 8 bits.
TEST(TypeParameterSim, PropertyDeclaredThroughAClassTypeNameIsItsWidth) {
  struct Form {
    const char* classes;
    const char* type;
  };
  const Form kForms[] = {
      {"class P; typedef byte I; I y; endclass", "P"},
      {"class P; localparam type I = byte; I y; endclass", "P"},
      {"class P; typedef X::T I; I y; endclass", "P"},
      {"class P; localparam type I = X::T; I y; endclass", "P"},
      {"class P; X::T y; endclass", "P"},
      {"typedef byte U; class P; U y; endclass", "P"},
      {"class P #(type C = X); typedef C::T I; I y; endclass", "P"},
      {"class P #(type C = int); typedef C::T I; I y; endclass", "P #(X)"},
      {"class P #(type C = int); localparam type I = C::T; I y; endclass",
       "P #(.C(X))"},
  };
  for (const Form& form : kForms) {
    SCOPED_TRACE(form.classes);
    const std::string kSrc =
        std::string("class X; typedef byte T; endclass\n") + form.classes +
        "\nmodule t;\n"
        "  bit [63:0] r;\n  " +
        form.type +
        " o;\n"
        "  initial begin\n"
        "    o = new;\n"
        "    o.y = 40'h12_3456_789A;\n"
        "    r = {$bits(o.y), o.y};\n"
        "  end\n"
        "endmodule\n";
    EXPECT_EQ(RunAndGet(kSrc, "r"), (uint64_t{8} << 8) | 0x9Au);
  }
}

}  // namespace
