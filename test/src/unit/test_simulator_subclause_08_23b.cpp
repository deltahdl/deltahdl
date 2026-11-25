#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

const char* const kPackageClassTypeSrc =
    "package p;\n"
    "  class C; typedef byte b; endclass\n"
    "endpackage\n"
    "package q;\n"
    "  class C #(int W = 1); typedef int U; parameter type T = int; endclass\n"
    "endpackage\n"
    "package rp;\n"
    "  p::C::b a;\n"
    "  typedef p::C::b tb;\n"
    "  tb b;\n"
    "  int pw;\n"
    "endpackage\n"
    "typedef p::C::b ub;\n"
    "class Q; typedef p::C::b qb; qb m; p::C::b n; endclass\n"
    "module n #(type V = p::C::b) (); V z; endmodule\n"
    "interface ifc; p::C::b a; typedef p::C::b tb; tb b; endinterface\n"
    "program pr;\n"
    "  p::C::b a;\n"
    "  typedef p::C::b tb;\n"
    "  tb b;\n"
    "  initial begin rp::pw = $bits(a) * 100 + $bits(b); #5; end\n"
    "endprogram\n"
    "function int uf(); p::C::b a; typedef p::C::b tb; tb b; return $bits(a) * "
    "100 + $bits(b); endfunction\n"
    "module top;\n"
    "  p::C::b y;\n"
    "  typedef p::C::b tb;\n"
    "  tb x;\n"
    "  ub u;\n"
    "  var type(p::C::b) w;\n"
    "  localparam type LV = p::C::b;\n"
    "  LV z;\n"
    "  Q qq = new;\n"
    "  n nn();\n"
    "  ifc ii();\n"
    "  pr pp();\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14;\n"
    "  initial begin\n"
    "    r1 = $bits(y); r2 = $bits(x); r3 = $bits(u); r4 = $bits(qq.m); r5 = "
    "$bits(qq.n);\n"
    "    r6 = $bits(w); r7 = $bits(z); r8 = $bits(nn.z); r9 = "
    "$bits(q::C#(4)::U); r10 = $bits(q::C#(4)::T);\n"
    "    r11 = $bits(ii.a) * 100 + $bits(ii.b); r13 = $bits(rp::a) * 100 + "
    "$bits(rp::b); r14 = uf();\n"
    "    #1 r12 = rp::pw;\n"
    "  end\n"
    "endmodule\n";

TEST(ClassScopeResolutionSim, PackageClassTypeDeclaresAVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(kPackageClassTypeSrc, f);
  LowerRunAndCheck(f, design, {{"r1", 8u}});
}

TEST(ClassScopeResolutionSim, PackageClassTypeHasItsWidthEverywhere) {
  SimFixture f;
  auto* design = ElaborateSrc(kPackageClassTypeSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r2", 8u},
                    {"r3", 8u},
                    {"r4", 8u},
                    {"r5", 8u},
                    {"r6", 8u},
                    {"r7", 8u},
                    {"r8", 8u},
                    {"r9", 32u},
                    {"r10", 32u},
                    {"r11", 808u},
                    {"r12", 808u},
                    {"r13", 808u},
                    {"r14", 808u}});
}

constexpr std::string_view kSameNamedClasses =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  class K;\n"
    "    typedef byte inner; typedef t viat; typedef inner again;\n"
    "    typedef shortint sh;\n"
    "    typedef struct packed { logic [3:0] hi; inner lo; } st;\n"
    "    class NK; typedef again deep; endclass\n"
    "  endclass\n"
    "  class D extends K; typedef inner fromk; endclass\n"
    "endpackage\n"
    "package pj; class K; typedef shortint inner; endclass endpackage\n"
    "class K; typedef logic [8:0] inner; endclass\n"
    "class Q; pk::K::inner x; pj::K::inner y; K::inner z; endclass\n";

std::string InTopWithSameNamedClasses(std::string_view items) {
  return std::string(kSameNamedClasses) + "module top;\n" + std::string(items) +
         "endmodule\n";
}

TEST(ClassScopeResolutionSim, PackageClassTypeIsThatOfThePackageNamed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithSameNamedClasses(
          "  typedef pk::K::inner ta; typedef pj::K::inner tb;\n"
          "  ta a; tb b; Q q = new;\n"
          "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10;\n"
          "  initial begin\n"
          "    pk::K::inner x; pj::K::inner y; K::inner z;\n"
          "    r1 = $bits(x); r2 = $bits(y); r3 = $bits(z);\n"
          "    r4 = $bits(a); r5 = $bits(b);\n"
          "    r6 = $bits(q.x); r7 = $bits(q.y); r8 = $bits(q.z);\n"
          "    r9 = $bits(pk::K::inner); r10 = $bits(pj::K::inner);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 8u},
                    {"r2", 16u},
                    {"r3", 9u},
                    {"r4", 8u},
                    {"r5", 16u},
                    {"r6", 8u},
                    {"r7", 16u},
                    {"r8", 9u},
                    {"r9", 8u},
                    {"r10", 16u}});
}

TEST(ClassScopeResolutionSim, PackageClassTypeNamesTheTypesAroundIt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithSameNamedClasses(
          "  typedef pk::K::viat ta; typedef pk::K::again tb;\n"
          "  typedef pk::K::NK::deep tc; typedef pk::D::fromk td;\n"
          "  ta a; tb b; tc c; td d;\n"
          "  int r1, r2, r3, r4;\n"
          "  initial begin\n"
          "    r1 = $bits(a); r2 = $bits(b); r3 = $bits(c); r4 = $bits(d);\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 12u}, {"r2", 8u}, {"r3", 8u}, {"r4", 8u}});
}

TEST(ClassScopeResolutionSim, PackageClassTypeSizesMembersCastsAndIndexes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithSameNamedClasses(
          "  typedef struct packed { pk::K::inner a; pk::K::sh b; } ts;\n"
          "  ts u;\n"
          "  int aa[pk::K::sh];\n"
          "  int r1, r2, r3, r4, r5, r6;\n"
          "  initial begin\n"
          "    var type(pk::K::inner) v;\n"
          "    struct { pk::K::inner a; pk::K::sh b; } s;\n"
          "    aa[65535] = 3;\n"
          "    r1 = $bits(u); r2 = $bits(s); r3 = pk::K::inner'(300);\n"
          "    r4 = aa[-1]; r5 = $bits(v); r6 = $bits(type(pk::K::inner));\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 24u},
                    {"r2", 24u},
                    {"r3", 44u},
                    {"r4", 3u},
                    {"r5", 8u},
                    {"r6", 8u}});
}

TEST(ClassScopeResolutionSim, PackageClassStructureTypeSelectsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithSameNamedClasses(
          "  pk::K::st s = 12'ha3c; typedef pk::K::st ts; ts u = 12'h123;\n"
          "  int r1, r2, r3, r4, r5, r6;\n"
          "  initial begin\n"
          "    pk::K::st v; v = 12'h456;\n"
          "    r1 = s.hi; r2 = s.lo; r3 = u.hi; r4 = u.lo;\n"
          "    r5 = v.hi; r6 = v.lo;\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 0xau},
                    {"r2", 0x3cu},
                    {"r3", 1u},
                    {"r4", 0x23u},
                    {"r5", 4u},
                    {"r6", 0x56u}});
}

TEST(ClassScopeResolutionSim, PackageClassTypeIsComparedAsItself) {
  SimFixture f;
  auto* design = ElaborateSrc(
      InTopWithSameNamedClasses(
          "  int r1, r2, r3;\n"
          "  if (type(pk::K::inner) == type(byte)) initial r1 = 1;\n"
          "  else initial r1 = 2;\n"
          "  if (type(pk::K::inner) == type(pj::K::inner)) initial r2 = 1;\n"
          "  else initial r2 = 2;\n"
          "  initial r3 = type(pj::K::inner) == type(shortint) ? 1 : 2;\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 2u}, {"r3", 1u}});
}

TEST(ClassScopeResolutionSim,
     PackageClassSpecializationTypeIsComparedAsItself) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  class C #(int W = 1, type T = int);\n"
      "    typedef bit [W-1:0] v; typedef T u;\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  int r1, r2, r3, r4;\n"
      "  if (type(q::C#(4)::v) == type(bit [3:0])) initial r1 = 1;\n"
      "  else initial r1 = 2;\n"
      "  if (type(q::C#(4)::v) == type(q::C#(5)::v)) initial r2 = 1;\n"
      "  else initial r2 = 2;\n"
      "  if (type(q::C#(.W(), .T(byte))::u) == type(byte)) initial r3 = 1;\n"
      "  else initial r3 = 2;\n"
      "  var type(q::C#(4)::v) x;\n"
      "  initial r4 = $bits(x);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 2u}, {"r3", 1u}, {"r4", 4u}});
}

TEST(ClassScopeResolutionSim, TypeReferenceTakesTheSpecializationsArguments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  class C #(int W = 1, type T = int);\n"
      "    typedef bit [W-1:0] v; typedef T u;\n"
      "  endclass\n"
      "  class D; typedef byte b; endclass\n"
      "  typedef bit [3:0] nib;\n"
      "endpackage\n"
      "class E #(type T = int, int W = 1); static int w = W; endclass\n"
      "class C #(int W = 1, type T = int);\n"
      "  typedef bit [W-1:0] v; typedef T u;\n"
      "endclass\n"
      "module top;\n"
      "  localparam int P = 8'h35;\n"
      "  typedef bit [3:0] nib4;\n"
      "  localparam struct packed { bit [3:0] hi; bit [3:0] lo; } SP = 8'h35;\n"
      "  var type(q::C#(P)::v) a;\n"
      "  var type(q::C#(P[3:0])::v) b;\n"
      "  var type(q::C#(P[0])::v) c;\n"
      "  var type(q::C#(P[0 +: 3])::v) d;\n"
      "  var type(q::C#(P[5 -: 2])::v) e;\n"
      "  var type(q::C#(SP.lo[1:0])::v) g;\n"
      "  var type(q::C#(1, nib4 [1:0])::u) h;\n"
      "  var type(q::C#(1, bit [1:0][2:0])::u) i;\n"
      "  var type(q::C#(1, q::nib)::u) j;\n"
      "  var type(q::C#(1, q::nib [2:0])::u) k;\n"
      "  var type(q::C#(1, q::D::b)::u) l;\n"
      "  var type(C#(P[3:0])::v) m;\n"
      "  var type(C#(1, byte)::u) n;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14;\n"
      "  initial begin\n"
      "    r1 = $bits(a); r2 = $bits(b); r3 = $bits(c); r4 = $bits(d);\n"
      "    r5 = $bits(e); r6 = $bits(g); r7 = $bits(h); r8 = $bits(i);\n"
      "    r9 = $bits(j); r10 = $bits(k); r11 = $bits(l); r12 = $bits(m);\n"
      "    r13 = $bits(n); r14 = E#(type(a), 4)::w;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 53u},
                    {"r2", 5u},
                    {"r3", 1u},
                    {"r4", 5u},
                    {"r5", 3u},
                    {"r6", 1u},
                    {"r7", 8u},
                    {"r8", 6u},
                    {"r9", 4u},
                    {"r10", 12u},
                    {"r11", 8u},
                    {"r12", 5u},
                    {"r13", 8u},
                    {"r14", 4u}});
}

}  // namespace
