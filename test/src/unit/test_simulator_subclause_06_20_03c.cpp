#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

std::string InTop(std::string_view before, std::string_view items) {
  return std::string(before) +
         "module top;\n"
         "  int r1, r2, r3, r4, r5, r6, r7;\n" +
         std::string(items) + "endmodule\n";
}

TEST(InPlaceTypeParameterSim, ModuleHeaderDefaultIsAnEnumeration) {
  SimFixture f;
  auto* design =
      ElaborateSrc(InTop("module m #(parameter type T = enum { A, B },\n"
                         "           type U = enum logic [1:0] { C, D = 3 },\n"
                         "           int N = B + 1) (input logic [N-1:0] i);\n"
                         "  T v;\n"
                         "  U w;\n"
                         "  int sum = B + D;\n"
                         "  initial begin\n"
                         "    v = B;\n"
                         "    w = D;\n"
                         "    if (w.name() == \"D\") top.r1 = $bits(v);\n"
                         "    top.r2 = v;\n"
                         "    top.r3 = $bits(w);\n"
                         "    top.r4 = w;\n"
                         "    top.r5 = sum;\n"
                         "    top.r6 = $bits(i);\n"
                         "  end\n"
                         "endmodule\n",
                         "  m u(0);\n"
                         "  initial #1 r7 = u.B;\n"),
                   f);
  LowerRunAndCheck(f, design,
                   {{"r1", 32u},
                    {"r2", 1u},
                    {"r3", 2u},
                    {"r4", 3u},
                    {"r5", 4u},
                    {"r6", 2u},
                    {"r7", 1u}});
}

TEST(InPlaceTypeParameterSim, ModuleHeaderDefaultIsAStructureOrUnion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("module m #(type S = struct packed { logic [3:0] a; bit b; },\n"
            "           type R = struct { int a; real b; },\n"
            "           type U = union packed { bit [7:0] a; bit [7:0] b; },\n"
            "           type P = struct packed { bit [3:0] a; bit b; } [2:0],\n"
            "           type G = struct packed signed { logic [3:0] a; },\n"
            "           type E = struct packed { enum bit { A, B } e; bit y; })"
            " ();\n"
            "  S s;\n"
            "  R r;\n"
            "  int sum;\n"
            "  U u;\n"
            "  P p;\n"
            "  G g;\n"
            "  E e;\n"
            "  initial begin\n"
            "    s.a = 9;\n"
            "    s.b = 1;\n"
            "    r.b = 1.5;\n"
            "    r.a = $bits(s);\n"
            "    u.a = 200;\n"
            "    p = 0;\n"
            "    p[1].a = 9;\n"
            "    g = -2;\n"
            "    e.e = B;\n"
            "    e.y = 0;\n"
            "    top.r1 = s;\n"
            "    sum = r.a * 10 + r.b * 2;\n"
            "    top.r2 = sum;\n"
            "    top.r3 = u.b;\n"
            "    top.r4 = p;\n"
            "    top.r5 = $bits(p);\n"
            "    top.r6 = g;\n"
            "    top.r7 = e;\n"
            "  end\n"
            "endmodule\n",
            "  m u();\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 19u},
                    {"r2", 53u},
                    {"r3", 200u},
                    {"r4", 576u},
                    {"r5", 15u},
                    {"r6", 4294967294u},
                    {"r7", 2u}});
}

TEST(InPlaceTypeParameterSim, ModuleBodyDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("",
            "  parameter type T = enum { A, B };\n"
            "  parameter type S = struct packed { logic [3:0] a; bit b; },\n"
            "                 U = union packed { bit [7:0] a; bit [7:0] b; };\n"
            "  parameter type R = struct { real a; int b; };\n"
            "  localparam type L = enum bit [2:0] { C = 5, D };\n"
            "  localparam type M = L;\n"
            "  T t;\n"
            "  S s;\n"
            "  U u;\n"
            "  R r;\n"
            "  L l = D;\n"
            "  M m = C;\n"
            "  if (type(L) == type(M) && type(L) != type(T)) begin : g\n"
            "    int z = D;\n"
            "  end\n"
            "  initial begin\n"
            "    t = B;\n"
            "    s.a = 3;\n"
            "    s.b = 0;\n"
            "    u.a = 130;\n"
            "    r.a = 2.5;\n"
            "    r1 = t;\n"
            "    r2 = s;\n"
            "    r3 = u.b;\n"
            "    r4 = r.a * 2;\n"
            "    r5 = l;\n"
            "    r6 = m;\n"
            "    #1 r7 = g.z;\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 6u},
                    {"r3", 130u},
                    {"r4", 5u},
                    {"r5", 6u},
                    {"r6", 5u},
                    {"r7", 6u}});
}

TEST(InPlaceTypeParameterSim, InterfaceAndProgramDefaultsAreWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("interface ifc #(type T = enum { A, B }) ();\n"
            "  parameter type S = struct packed { bit [4:0] a; bit b; };\n"
            "  T v;\n"
            "  S s;\n"
            "  initial v = B;\n"
            "endinterface\n"
            "program p #(type T = enum bit [3:0] { C = 7, D }) ();\n"
            "  localparam type S = struct packed { bit [6:0] a; };\n"
            "  T v;\n"
            "  S s;\n"
            "  initial begin\n"
            "    #2 v = D;\n"
            "    top.r5 = v;\n"
            "    top.r6 = $bits(v);\n"
            "    top.r7 = $bits(s);\n"
            "  end\n"
            "endprogram\n",
            "  ifc i();\n"
            "  p q();\n"
            "  initial #1 begin\n"
            "    r1 = i.v;\n"
            "    r2 = i.B;\n"
            "    r3 = $bits(i.s);\n"
            "    r4 = $bits(i.v);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 6u},
                    {"r4", 32u},
                    {"r5", 8u},
                    {"r6", 4u},
                    {"r7", 7u}});
}

TEST(InPlaceTypeParameterSim, ClassHeaderDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("class W #(type T = enum logic [1:0] { A, B },\n"
            "          type U = struct packed { logic [3:0] a; bit b; },\n"
            "          type N = enum { E[2] = 4 });\n"
            "  T v;\n"
            "  U w;\n"
            "  static function T last(); return B; endfunction\n"
            "  function string named(); v = B; return v.name(); endfunction\n"
            "  function int numbered(); return E1; endfunction\n"
            "endclass\n",
            "  W #() h = new;\n"
            "  initial begin\n"
            "    h.w.a = 7;\n"
            "    if (h.named() == \"B\") r1 = h.v;\n"
            "    r2 = $bits(h.v);\n"
            "    r3 = h.w.a;\n"
            "    r4 = $bits(h.w);\n"
            "    r5 = W#()::B;\n"
            "    r6 = W#()::last();\n"
            "    r7 = h.numbered();\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 2u},
                    {"r3", 7u},
                    {"r4", 5u},
                    {"r5", 1u},
                    {"r6", 1u},
                    {"r7", 5u}});
}

TEST(InPlaceTypeParameterSim, ClassBodyDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("class W;\n"
            "  localparam type T = enum logic [1:0] { A, B };\n"
            "  parameter type U = struct packed { logic [3:0] a; bit b; };\n"
            "  T v;\n"
            "  U w;\n"
            "  function string named(); v = B; return v.name(); endfunction\n"
            "endclass\n",
            "  W h = new;\n"
            "  W::T z = W::B;\n"
            "  initial begin\n"
            "    h.w.a = 7;\n"
            "    if (h.named() == \"B\") r1 = h.v;\n"
            "    r2 = $bits(h.v);\n"
            "    r3 = h.w.a;\n"
            "    r4 = $bits(h.w);\n"
            "    r5 = z;\n"
            "  end\n"),
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 1u}, {"r2", 2u}, {"r3", 7u}, {"r4", 5u}, {"r5", 1u}});
}

TEST(InPlaceTypeParameterSim, PackageDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("package p;\n"
            "  parameter type T = enum bit [1:0] { A, B, C };\n"
            "  localparam type U = struct packed { logic [3:0] a; bit b; };\n"
            "  T v = C;\n"
            "  U w = 5'd13;\n"
            "endpackage\n",
            "  import p::*;\n"
            "  p::T x = p::B;\n"
            "  T y;\n"
            "  U z;\n"
            "  initial begin\n"
            "    y = B;\n"
            "    z.a = 4;\n"
            "    r1 = x;\n"
            "    if (y.name() == \"B\") r2 = y;\n"
            "    r3 = z.a;\n"
            "    r4 = $bits(p::T);\n"
            "    r5 = $bits(z);\n"
            "    r6 = p::v;\n"
            "    r7 = p::w.a;\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 4u},
                    {"r4", 2u},
                    {"r5", 5u},
                    {"r6", 2u},
                    {"r7", 6u}});
}

TEST(InPlaceTypeParameterSim, CompilationUnitDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("parameter type T = enum bit [1:0] { A, B, C };\n"
            "localparam type U = struct { real r; int i; };\n"
            "function automatic string named(T x); return x.name();\n"
            "endfunction\n",
            "  T y = B;\n"
            "  U z;\n"
            "  initial begin\n"
            "    z.r = 2.5;\n"
            "    if (named(C) == \"C\") r1 = y;\n"
            "    r2 = z.r * 2;\n"
            "    r3 = $bits(T);\n"
            "    r4 = $unit::C;\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 5u}, {"r3", 2u}, {"r4", 2u}});
}

TEST(InPlaceTypeParameterSim, GenerateBlockDefaultIsWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("",
            "  if (1) begin : g\n"
            "    parameter type T = enum { A, B },\n"
            "                   U = struct packed { bit [2:0] z; bit y; };\n"
            "    T q = B;\n"
            "    U s;\n"
            "    initial begin\n"
            "      s = 9;\n"
            "      r1 = q;\n"
            "      r2 = s.z;\n"
            "      r3 = g.B;\n"
            "    end\n"
            "  end\n"
            "  for (genvar i = 0; i < 2; i++) begin : h\n"
            "    localparam type T = enum { C = i + 4, D };\n"
            "    T q = D;\n"
            "  end\n"
            "  initial #1 begin r4 = h[0].q; r5 = h[1].q; end\n"),
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 1u}, {"r2", 4u}, {"r3", 1u}, {"r4", 5u}, {"r5", 6u}});
}

TEST(InPlaceTypeParameterSim, SubroutineAndBlockDefaultsAreWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("",
            "  function int f();\n"
            "    localparam type T = enum { A, B };\n"
            "    T q;\n"
            "    q = B;\n"
            "    return q;\n"
            "  endfunction\n"
            "  task t();\n"
            "    parameter type T = union packed { bit [2:0] a; bit [2:0] b; };"
            "\n"
            "    T z;\n"
            "    z.a = 5;\n"
            "    r2 = z.b;\n"
            "  endtask\n"
            "  initial begin\n"
            "    localparam type S = struct packed { bit [2:0] a; bit b; };\n"
            "    localparam type R = struct { int a; real b; };\n"
            "    localparam type E = enum bit [1:0] { C, D, F };\n"
            "    S s;\n"
            "    R r;\n"
            "    E e;\n"
            "    s = 0;\n"
            "    s.a = 5;\n"
            "    r.b = 1.5;\n"
            "    e = F;\n"
            "    r1 = f();\n"
            "    t();\n"
            "    r3 = s;\n"
            "    r4 = r.b * 2;\n"
            "    if (e.name() == \"F\") r5 = $bits(e);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 1u}, {"r2", 5u}, {"r3", 10u}, {"r4", 3u}, {"r5", 2u}});
}

TEST(InPlaceTypeParameterSim, InstanceOverridesTakeATypeWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("module m #(type T = int) (); T x; endmodule\n"
            "module b; parameter type T = int; T x; endmodule\n"
            "interface i #(type T = int) (); T x; endinterface\n"
            "program p #(type T = int) ();\n"
            "  T x;\n"
            "  initial #2 top.r7 = $bits(x);\n"
            "endprogram\n",
            "  m #(.T(struct packed { logic [3:0] a; })) u();\n"
            "  m #(struct packed { logic [4:0] a; }) v();\n"
            "  m #(enum logic [2:0] { E, F }) w();\n"
            "  b #(.T(union packed { logic [8:0] z; bit [8:0] y; })) x();\n"
            "  i #(.T(struct packed { bit [1:0] a; } [3:0])) y();\n"
            "  p #(struct packed { logic [9:0] a; }) z();\n"
            "  initial #1 begin\n"
            "    u.x.a = 9;\n"
            "    r1 = u.x;\n"
            "    r2 = $bits(v.x);\n"
            "    r3 = $bits(w.x);\n"
            "    r4 = $bits(x.x);\n"
            "    r5 = $bits(y.x);\n"
            "    r6 = $bits(u.x);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 9u},
                    {"r2", 5u},
                    {"r3", 3u},
                    {"r4", 9u},
                    {"r5", 8u},
                    {"r6", 4u},
                    {"r7", 10u}});
}

TEST(InPlaceTypeParameterSim, OverriddenDefaultStillDeclaresItsConstants) {
  SimFixture f;
  auto* design =
      ElaborateSrc(InTop("module m #(type T = enum { A, B = 6 }) ();\n"
                         "  T x;\n"
                         "  int b = B;\n"
                         "endmodule\n"
                         "module n;\n"
                         "  parameter type T = enum { A, B = 5 };\n"
                         "  T x;\n"
                         "  int b = B;\n"
                         "endmodule\n",
                         "  m #(byte) u();\n"
                         "  n #(.T(struct packed { bit [2:0] q; })) v();\n"
                         "  initial #1 begin\n"
                         "    r1 = u.b;\n"
                         "    r2 = $bits(u.x);\n"
                         "    r3 = v.b;\n"
                         "    r4 = $bits(v.x);\n"
                         "  end\n"),
                   f);
  LowerRunAndCheck(f, design, {{"r1", 6u}, {"r2", 8u}, {"r3", 5u}, {"r4", 3u}});
}

TEST(InPlaceTypeParameterSim, ClassSpecializationTakesATypeWrittenInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("class X #(type T = int); T v; endclass\n"
            "class Y extends X #(struct packed { bit [5:0] a; }); endclass\n",
            "  X #(struct packed { logic [3:0] a; }) h = new;\n"
            "  X #(.T(enum bit [2:0] { A, B })) k = new;\n"
            "  Y y = new;\n"
            "  initial begin\n"
            "    h.v.a = 5;\n"
            "    r1 = h.v;\n"
            "    r2 = $bits(h.v);\n"
            "    r3 = $bits(k.v);\n"
            "    r4 = $bits(y.v);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}, {"r2", 4u}, {"r3", 3u}, {"r4", 6u}});
}

TEST(InPlaceTypeParameterSim, ClassPropertyHasTheMembersOfItsArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("package pk;\n"
            "  typedef struct packed { bit [5:0] a; bit b; } s7;\n"
            "endpackage\n"
            "typedef struct packed { logic [3:0] a; logic [1:0] b; } s6;\n"
            "class X #(type T = s6); T v; endclass\n",
            "  X #(struct packed { logic [2:0] a; logic b; }) h = new;\n"
            "  X #(pk::s7) k = new;\n"
            "  X #() d = new;\n"
            "  X #(struct { int a; int b; }) u = new;\n"
            "  X #(struct packed { logic [1:0] a; } [1:0]) p = new;\n"
            "  initial begin\n"
            "    h.v = 13;\n"
            "    r1 = h.v.a;\n"
            "    h.v.b = 0;\n"
            "    r2 = h.v;\n"
            "    k.v.a = 33;\n"
            "    r3 = k.v.a;\n"
            "    d.v.a = 9;\n"
            "    r4 = d.v.a;\n"
            "    u.v.a = 70;\n"
            "    u.v.b = 8;\n"
            "    r5 = u.v.a + u.v.b;\n"
            "    r6 = $bits(p.v);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 6u},
                    {"r2", 12u},
                    {"r3", 33u},
                    {"r4", 9u},
                    {"r5", 78u},
                    {"r6", 4u}});
}

TEST(InPlaceTypeParameterSim, EachTypeWrittenInPlaceIsItsOwnSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTop("typedef struct packed { bit [2:0] a; } s3;\n"
            "class X #(type T = int); T v; static int s; endclass\n",
            "  X #(enum bit [2:0] { A, B }) h = new;\n"
            "  X #(enum bit [1:0] { C, D }) k = new;\n"
            "  initial begin\n"
            "    X#(struct packed { bit [2:0] a; })::s = 4;\n"
            "    X#(s3)::s = 6;\n"
            "    r1 = X#(struct packed { bit [2:0] a; })::s;\n"
            "    r2 = X#(s3)::s;\n"
            "    r3 = X#(int)::s;\n"
            "    r4 = $bits(h.v);\n"
            "    r5 = $bits(k.v);\n"
            "  end\n"),
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 0u}, {"r2", 6u}, {"r3", 0u}, {"r4", 3u}, {"r5", 2u}});
}

}  // namespace
