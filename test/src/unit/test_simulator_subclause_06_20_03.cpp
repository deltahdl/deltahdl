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

TEST(TypeParameterSim, PortsTakeEachInstancesOverridingType) {
  const char* const kOrders[] = {
      "  ma #(.TP(logic [15:0])) u(x, y);\n  ma v(p, q);\n",
      "  ma v(p, q);\n  ma #(.TP(logic [15:0])) u(x, y);\n",
  };
  for (const char* order : kOrders) {
    SCOPED_TRACE(order);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string("module ma #(parameter type TP = logic "
                                     "[7:0]) (input TP a, output TP b);\n"
                                     "  assign b = a;\n"
                                     "endmodule\n"
                                     "module t;\n"
                                     "  logic [15:0] x = 16'hABCD, y;\n"
                                     "  logic [15:0] p = 16'hABCD, q;\n") +
                             order +
                             "  initial #1 $display(\"%0d %0d %h %0d %0d "
                             "%h\", $bits(u.a), $bits(u.b), y, $bits(v.a), "
                             "$bits(v.b), q);\n"
                             "endmodule\n",
                         f),
              "16 16 abcd 8 8 00cd\n");
  }
}

TEST(TypeParameterSim, InterfaceDataTakesTheOverridingType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc #(parameter type T = byte);\n"
                       "  T d;\n"
                       "endinterface\n"
                       "module t;\n"
                       "  ifc #(.T(shortint)) i();\n"
                       "  initial begin\n"
                       "    i.d = 70000;\n"
                       "    #1 $display(\"%0d %0d\", $bits(i.d), i.d);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "16 4464\n");
}

TEST(TypeParameterSim, ProgramDataTakesEachInstancesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program prg #(parameter type T = byte, "
                       "parameter int D = 1);\n"
                       "  T d;\n"
                       "  initial #D begin\n"
                       "    d = 300;\n"
                       "    $display(\"%0d %0d\", $bits(d), d);\n"
                       "  end\n"
                       "endprogram\n"
                       "module t;\n"
                       "  prg #(.T(int)) p();\n"
                       "  prg #(.D(2)) r();\n"
                       "endmodule\n",
                       f),
            "32 300\n8 44\n");
}

TEST(TypeParameterSim, InterfaceInstancesKeepTheirOwnTypes) {
  const char* const kOrders[] = {
      "  I u();\n  I #(.T(int)) v();\n  I #(int) w();\n",
      "  I #(int) w();\n  I #(.T(int)) v();\n  I u();\n",
  };
  for (const char* order : kOrders) {
    SCOPED_TRACE(order);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string("interface I #(parameter type T = logic "
                                     "[3:0]);\n"
                                     "  T d;\n"
                                     "endinterface\n"
                                     "module t;\n") +
                             order +
                             "  initial begin\n"
                             "    u.d = 5'h1F;\n"
                             "    v.d = -1;\n"
                             "    w.d = -1;\n"
                             "    #1 $display(\"%0d %h %0d %0d %0d %0d\", "
                             "$bits(u.d), u.d, $bits(v.d), v.d < 0, "
                             "$bits(w.d), w.d < 0);\n"
                             "  end\n"
                             "endmodule\n",
                         f),
              "4 f 32 1 32 1\n");
  }
}

}  // namespace
