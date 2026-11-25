#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

constexpr std::string_view kPackageTypesAndClasses =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  typedef struct packed { bit [2:0] z; } st;\n"
    "  typedef enum { A, B } en;\n"
    "  parameter int N = 3;\n"
    "  class K; typedef byte inner; int z = 7; endclass\n"
    "  class PX #(type T = int); T v; endclass\n"
    "endpackage\n"
    "package pj;\n"
    "  typedef logic [3:0] t;\n"
    "  typedef enum { C, D } en;\n"
    "  class K; int z = 2; endclass\n"
    "endpackage\n"
    "typedef logic [6:0] ut;\n"
    "class K; int z = 1; endclass\n"
    "class X #(type T = int); T v; static int s; endclass\n"
    "class C #(type T = int); typedef T u; endclass\n"
    "class I #(type T = int, int W = 2); T v; bit [W-1:0] w; endclass\n";

std::string InTopWithPackageTypes(std::string_view items) {
  return std::string(kPackageTypesAndClasses) + "module top;\n" +
         "  int r1, r2, r3, r4, r5, r6, r7;\n" + std::string(items) +
         "endmodule\n";
}

TEST(TypeParameterSim, BodyDefaultNamesATypeOfAPackage) {
  SimFixture f;
  auto* design =
      ElaborateSrc(InTopWithPackageTypes("  parameter type T = pk::t;\n"
                                         "  parameter type U = $unit::ut;\n"
                                         "  parameter type V = pk::K::inner;\n"
                                         "  T x; U y; V z;\n"
                                         "  initial begin\n"
                                         "    r1 = $bits(x);\n"
                                         "    r2 = $bits(y);\n"
                                         "    r3 = $bits(z);\n"
                                         "  end\n"),
                   f);
  LowerRunAndCheck(f, design, {{"r1", 12u}, {"r2", 7u}, {"r3", 8u}});
}

TEST(TypeParameterSim, HeaderDefaultNamesATypeOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kPackageTypesAndClasses) +
          "package out; int p; endpackage\n"
          "module m #(parameter type MT = pk::t, type MU = $unit::ut) ();\n"
          "  MT x; MU y; int r; initial r = $bits(x) * 100 + $bits(y);\n"
          "endmodule\n"
          "interface ifc #(parameter type MT = pk::t, type MU = $unit::ut) "
          "();\n"
          "  MT x; MU y; int r; initial r = $bits(x) * 100 + $bits(y);\n"
          "endinterface\n"
          "program pr #(parameter type MT = pk::t, type MU = $unit::ut) ();\n"
          "  MT x; MU y; initial begin out::p = $bits(x) * 100 + $bits(y); "
          "#5;\n"
          "  end\n"
          "endprogram\n"
          "class W #(type T = pk::t, type U = $unit::ut);\n"
          "  T x; U y;\n"
          "endclass\n"
          "class WK #(type T = pk::K, type U = pk::K::inner);\n"
          "  T x; U y;\n"
          "endclass\n"
          "module top;\n"
          "  m mm(); ifc ii(); pr pp(); W w = new; WK wk = new;\n"
          "  int r1, r2, r3, r4, r5, r6;\n"
          "  initial begin\n"
          "    wk.x = new;\n"
          "    r4 = $bits(w.x) * 100 + $bits(w.y);\n"
          "    r5 = wk.x.z; r6 = $bits(wk.y);\n"
          "    #1 r1 = mm.r; r2 = ii.r; r3 = out::p;\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1207u},
                    {"r2", 1207u},
                    {"r3", 1207u},
                    {"r4", 1207u},
                    {"r5", 7u},
                    {"r6", 8u}});
}

TEST(TypeParameterSim, SpecializationTakesATypeOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  X #(pk::t) a = new; X #(.T(pk::t)) b = new;\n"
          "  typedef X #(pk::t) xt; xt c = new;\n"
          "  X #(pk::t [1:0]) d = new; X #(pk::K::inner) e = new;\n"
          "  X #($unit::ut) g = new;\n"
          "  pk::PX #(pk::t) i = new;\n"
          "  initial begin\n"
          "    r1 = $bits(a.v); r2 = $bits(b.v); r3 = $bits(c.v);\n"
          "    r4 = $bits(d.v); r5 = $bits(e.v); r6 = $bits(g.v);\n"
          "    r7 = $bits(i.v);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 12u},
                    {"r2", 12u},
                    {"r3", 12u},
                    {"r4", 24u},
                    {"r5", 8u},
                    {"r6", 7u},
                    {"r7", 12u}});
}

TEST(TypeParameterSim, ProceduralSpecializationTakesATypeOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  function automatic int fn();\n"
          "    X #(pk::t) a = new; return $bits(a.v);\n"
          "  endfunction\n"
          "  if (1) begin : g\n"
          "    X #(pk::t) a = new;\n"
          "  end\n"
          "  initial begin\n"
          "    X #(pk::t) a; X #(.T(pk::t)) b; X #(pk::t [1:0]) c;\n"
          "    X #(pk::K::inner) d; X #(X #(pk::t)) e;\n"
          "    a = new; b = new; c = new; d = new; e = new; e.v = new;\n"
          "    r1 = $bits(a.v); r2 = $bits(b.v); r3 = $bits(c.v);\n"
          "    r4 = $bits(d.v); r5 = fn(); r6 = $bits(g.a.v);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 12u},
                    {"r2", 12u},
                    {"r3", 24u},
                    {"r4", 8u},
                    {"r5", 12u},
                    {"r6", 12u}});
}

TEST(TypeParameterSim, SpecializationTakesPackageTypesBesidePackageValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  I #(pk::t, pk::N) a = new; I #(.W(pk::N), .T(pk::t)) b = new;\n"
          "  I #(.W(pk::N)) c = new;\n"
          "  initial begin\n"
          "    r1 = $bits(a.v); r2 = $bits(a.w); r3 = $bits(b.v);\n"
          "    r4 = $bits(b.w); r5 = $bits(c.v); r6 = $bits(c.w);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 12u},
                    {"r2", 3u},
                    {"r3", 12u},
                    {"r4", 3u},
                    {"r5", 32u},
                    {"r6", 3u}});
}

TEST(TypeParameterSim, SpecializationOfEveryScopeTakesATypeOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kPackageTypesAndClasses) +
          "package px;\n"
          "  int p;\n"
          "  class Q; pk::PX #(pk::t) a; endclass\n"
          "endpackage\n"
          "class Q;\n"
          "  X #(pk::t) a;\n"
          "endclass\n"
          "typedef struct { X #(pk::t) h; struct { X #(pk::st) i; } n; } st;\n"
          "typedef X #(pk::t) uxt;\n"
          "interface ifc; X #(pk::t) a = new; endinterface\n"
          "program pr; X #(pk::t) a = new;\n"
          "  initial begin px::p = $bits(a.v); #5; end\n"
          "endprogram\n"
          "module top;\n"
          "  Q q = new; px::Q pq = new; ifc ii(); pr pp();\n"
          "  pk::PX #(pk::t) x = new; uxt y = new; X #(pk::t) z = new;\n"
          "  st s; int r1, r2, r3, r4, r5;\n"
          "  initial begin\n"
          "    q.a = z; x.v = 16'h1234; pq.a = x;\n"
          "    z.v = 16'h5678;\n"
          "    r1 = q.a.v; r2 = pq.a.v;\n"
          "    r3 = $bits(ii.a.v); r4 = $bits(y.v);\n"
          "    #1 r5 = px::p;\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 0x678u}, {"r2", 0x234u}, {"r3", 12u}, {"r4", 12u}, {"r5", 12u}});
}

TEST(TypeParameterSim, BaseSpecializationTakesATypeOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kPackageTypesAndClasses) +
          "class Y1 extends X #(pk::t); endclass\n"
          "class Y2 extends X #(pk::K::inner); endclass\n"
          "class Y3 extends X #(.T(pk::st)); endclass\n"
          "interface class IC #(type T = int);\n"
          "  pure virtual function T get();\n"
          "endclass\n"
          "class Im implements IC #(pk::t);\n"
          "  virtual function pk::t get(); return '1; endfunction\n"
          "endclass\n"
          "interface class JC extends IC #(pk::t); endclass\n"
          "class Jm implements JC;\n"
          "  virtual function pk::t get(); return 5; endfunction\n"
          "endclass\n"
          "module top;\n"
          "  Y1 a = new; Y2 b = new; Y3 c = new; Im i = new; Jm j = new;\n"
          "  IC #(pk::t) h;\n"
          "  int r1, r2, r3, r4, r5;\n"
          "  initial begin\n"
          "    r1 = $bits(a.v); r2 = $bits(b.v); r3 = $bits(c.v);\n"
          "    h = i; r4 = h.get();\n"
          "    h = j; r5 = h.get();\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 12u}, {"r2", 8u}, {"r3", 3u}, {"r4", 4095u}, {"r5", 5u}});
}

TEST(TypeParameterSim, SpecializationOfAPackageTypeIsThatOfTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  X #(pk::t) a = new; X #(logic [11:0]) b;\n"
          "  X #(pk::K::inner) c = new; X #(byte) d; class M; endclass\n"
          "  initial begin\n"
          "    b = a; b.v = 5; r1 = a.v;\n"
          "    d = c; d.v = 6; r2 = c.v;\n"
          "    X#(pk::t)::s = 4; X#(pj::t)::s = 5;\n"
          "    r3 = X#(pk::t)::s * 10 + X#(pj::t)::s;\n"
          "    X#(pk::en)::s = 1; X#(pj::en)::s = 2;\n"
          "    r4 = X#(pk::en)::s * 10 + X#(pj::en)::s;\n"
          "    X#(pk::K)::s = 1; X#(pj::K)::s = 2; X#(K)::s = 3;\n"
          "    r5 = X#(pk::K)::s * 100 + X#(pj::K)::s * 10 + X#(K)::s;\n"
          "    X#(pk::K::inner)::s = 8; r6 = X#(byte)::s;\n"
          "    X#(M)::s = 9; r7 = X#(K)::s * 10 + X#(M)::s;\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 5u},
                    {"r2", 6u},
                    {"r3", 45u},
                    {"r4", 12u},
                    {"r5", 123u},
                    {"r6", 8u},
                    {"r7", 39u}});
}

TEST(TypeParameterSim, SpecializationHoldsObjectsOfThePackageClassNamed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  X #(pk::K) a = new; X #(pj::K) b = new; X #(K) c = new;\n"
          "  X #(pk::st) d = new;\n"
          "  mailbox #(pk::K) mk = new; mailbox #(pk::t) mt = new;\n"
          "  std::mailbox #(pk::t) ms = new;\n"
          "  initial begin\n"
          "    pk::K k; pk::t t; pk::K o;\n"
          "    a.v = new; b.v = new; c.v = new; d.v.z = 6;\n"
          "    r1 = a.v.z * 100 + b.v.z * 10 + c.v.z;\n"
          "    r2 = d.v.z; r3 = $bits(d.v);\n"
          "    k = new; k.z = 9; mk.put(k); mk.get(o); r4 = o.z;\n"
          "    mt.put(12'habc); mt.get(t); r5 = t;\n"
          "    ms.put(12'h123); ms.get(t); r6 = t;\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 721u},
                    {"r2", 6u},
                    {"r3", 3u},
                    {"r4", 9u},
                    {"r5", 0xabcu},
                    {"r6", 0x123u}});
}

TEST(TypeParameterSim, WeakReferenceTakesAClassOfAPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk; class K; endclass endpackage\n"
      "class U; endclass\n"
      "class Q;\n"
      "  weak_reference #(pk::K) w;\n"
      "  function new(pk::K k); w = new(k); endfunction\n"
      "endclass\n"
      "module top;\n"
      "  pk::K k = new; U u = new; Q q = new(k);\n"
      "  weak_reference #(pk::K) a; weak_reference #($unit::U) b;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    weak_reference #(pk::K) c;\n"
      "    a = new(k); b = new(u); c = new(k);\n"
      "    r1 = a.get() == k; r2 = b.get() == u; r3 = c.get() == k;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 1u}, {"r3", 1u}});
}

TEST(TypeParameterSim, SpecializationInASpecializedClassTakesAPackageType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  class O #(type T = int);\n"
          "    class I #(type U = int); U v; endclass\n"
          "  endclass\n"
          "  O#(pk::t)::I#(pk::t) a = new; O#(int)::I#(pk::K::inner) b = new;\n"
          "  initial begin r1 = $bits(a.v); r2 = $bits(b.v); end\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 12u}, {"r2", 8u}});
}

TEST(TypeParameterSim, TypeOfASpecializationFollowsItsPackageTypeArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithPackageTypes(
          "  C#(pk::t)::u a; C#(pk::K::inner)::u b; C#(.T(pk::t))::u c;\n"
          "  C#(pk::t [1:0])::u d;\n"
          "  var type(C#(pk::t)::u) e;\n"
          "  initial begin\n"
          "    C#(pk::t)::u p;\n"
          "    r1 = $bits(a); r2 = $bits(b); r3 = $bits(c); r4 = $bits(d);\n"
          "    r5 = $bits(e); r6 = $bits(p);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 12u},
                    {"r2", 8u},
                    {"r3", 12u},
                    {"r4", 24u},
                    {"r5", 12u},
                    {"r6", 12u}});
}

TEST(TypeParameterSim, InstanceTakesATypeOfAPackageClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kPackageTypesAndClasses) +
          "package out; int p; endpackage\n"
          "module m #(type T = int) (); T x; int r; initial r = $bits(x);\n"
          "endmodule\n"
          "interface ifc #(type T = int) (); T x; int r;\n"
          "  initial r = $bits(x);\n"
          "endinterface\n"
          "program pr #(type T = int) (); T x;\n"
          "  initial begin out::p = out::p * 100 + $bits(x); #5; end\n"
          "endprogram\n"
          "module top;\n"
          "  m #(.T(pk::K::inner)) a(); m #(pk::K::inner) b();\n"
          "  m #(pk::K::inner [1:0]) c();\n"
          "  ifc #(.T(pk::K::inner)) e(); ifc #(pk::K::inner) g();\n"
          "  pr #(.T(pk::K::inner)) p(); pr #(pk::K::inner) q();\n"
          "  int r1, r2, r3, r4, r5, r6;\n"
          "  initial begin\n"
          "    #1 r1 = a.r; r2 = b.r; r3 = c.r;\n"
          "    r4 = e.r; r5 = g.r; r6 = out::p;\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 8u},
                    {"r2", 8u},
                    {"r3", 16u},
                    {"r4", 8u},
                    {"r5", 8u},
                    {"r6", 808u}});
}

}  // namespace
