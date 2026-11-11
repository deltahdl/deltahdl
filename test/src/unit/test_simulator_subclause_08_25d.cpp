#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassParamsSim, EnumerationConstantOfTheClassGivesAParameterItsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C1;\n"
      "  typedef enum {A, B} e_t;\n"
      "  parameter e_t P1 = B;\n"
      "  localparam e_t L1 = B;\n"
      "  parameter int K = B;\n"
      "endclass\n"
      "class C2 #(parameter enum {X, Y} E = Y);\n"
      "endclass\n"
      "class C3 #(enum {M, N} F = N);\n"
      "endclass\n"
      "class C4;\n"
      "  typedef enum logic [2:0] {Q = 3, R = 5} q_t;\n"
      "  parameter q_t P4 = R;\n"
      "endclass\n"
      "class Outer;\n"
      "  class NC; typedef enum {A, Z, B} e_t; parameter e_t P = B; endclass\n"
      "endclass\n"
      "module top;\n"
      "  typedef enum {W0, W1, W2, B} me_t;\n"
      "  class MC; typedef enum {B, A} e_t; parameter e_t P = A; endclass\n"
      "  localparam int R1 = C1::P1;\n"
      "  localparam int R2 = C1::L1;\n"
      "  localparam int R3 = C1::K;\n"
      "  localparam int R4 = C2#()::E;\n"
      "  localparam int R5 = C3#()::F;\n"
      "  localparam int R6 = C4::P4;\n"
      "  localparam int R8 = Outer::NC::P;\n"
      "  localparam int R9 = MC::P;\n"
      "  localparam int R10 = B;\n"
      "  int r1, r2, r3, r4, r5, r6, r8, r9, r10;\n"
      "  initial begin\n"
      "    r1 = R1; r2 = R2; r3 = R3; r4 = R4; r5 = R5;\n"
      "    r6 = R6; r8 = R8; r9 = R9; r10 = R10;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 1u},
                    {"r4", 1u},
                    {"r5", 1u},
                    {"r6", 5u},
                    {"r8", 2u},
                    {"r9", 1u},
                    {"r10", 3u}});
}

TEST(ClassParamsSim,
     DISABLED_EnumerationConstantOfAPackageClassOrInPlaceTypeFolds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  class PC; typedef enum {A, B, Z} e_t; parameter e_t P = Z; endclass\n"
      "endpackage\n"
      "class C5;\n"
      "  parameter enum {G, H} PE = H;\n"
      "endclass\n"
      "module top;\n"
      "  localparam int R7 = pk::PC::P;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = R7;\n"
      "    r2 = C5::PE;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 2u}, {"r2", 1u}});
}

const char* const kTypeParameterSubroutineSrc =
    "class MemD #(type T = byte, int size = 1);\n"
    "  typedef T elem_t;\n"
    "  T held;\n"
    "  function T next(T a); return a + 1; endfunction\n"
    "  function T viaresult(T a); viaresult = a + 1; endfunction\n"
    "  function elem_t viatypedef(T a); return a + 1; endfunction\n"
    "  static function T snext(T a); return a + 1; endfunction\n"
    "  function T wide(); return 32'h12345678; endfunction\n"
    "  function int arg(T a); return a; endfunction\n"
    "  function void outs(output T o, inout T io, ref T r);\n"
    "    o = 32'h12345678; o = o >> 8;\n"
    "    io = 32'h12345678; io = io >> 8;\n"
    "    r = 32'h12345678; r = r >> 8;\n"
    "  endfunction\n"
    "  task targ(input T a, output int o); o = a; endtask\n"
    "  extern function T ext(T a);\n"
    "  function int keep(); T v; v = 32'h12345678; held = v; return v; "
    "endfunction\n"
    "  function logic [size-1:0] lw(); return 8'hFF; endfunction\n"
    "endclass\n"
    "function MemD::T MemD::ext(T a); return a + 1; endfunction\n"
    "class Ri #(type T = int); function T half(); return 1.5; endfunction "
    "endclass\n"
    "class Plain; function shortint p(); return 32'h12345678; endfunction "
    "endclass\n"
    "module top;\n"
    "  MemD#(shortint, 6) d = new;\n"
    "  MemD#(byte) b8 = new;\n"
    "  MemD#(logic [3:0]) l4 = new;\n"
    "  Ri#(int) ri = new;\n"
    "  Ri#(real) rr = new;\n"
    "  Plain pl = new;\n"
    "  shortint so, sio, sr;\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, "
    "r16;\n"
    "  initial begin\n"
    "    r1 = d.next(16'hFFFF);\n"
    "    r2 = d.viaresult(16'hFFFF);\n"
    "    r3 = d.viatypedef(16'hFFFF);\n"
    "    r4 = MemD#(shortint, 6)::snext(16'hFFFF);\n"
    "    r5 = d.wide();\n"
    "    r6 = $bits(d.next(1)) * 10000 + $bits(b8.next(1)) * 100 + "
    "$bits(l4.next(1));\n"
    "    r7 = d.next(16'h7FFF) < 0;\n"
    "    r8 = d.arg(32'h12345678);\n"
    "    d.outs(so, sio, sr);\n"
    "    r9 = so * 10000 + sio * 100 + sr;\n"
    "    d.targ(32'h12345678, r10);\n"
    "    r11 = d.ext(16'hFFFF);\n"
    "    r12 = ri.half();\n"
    "    r13 = rr.half() * 10;\n"
    "    r14 = d.keep();\n"
    "    r15 = pl.p();\n"
    "    r16 = d.lw();\n"
    "  end\n"
    "endmodule\n";

TEST(ClassSim, TypeParameterOutputsLocalsAndPropertiesTakeTheActual) {
  SimFixture f;
  auto* design = ElaborateSrc(kTypeParameterSubroutineSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r9", 868686u},
                    {"r12", 2u},
                    {"r13", 15u},
                    {"r14", 22136u},
                    {"r15", 22136u},
                    {"r16", 63u}});
}

TEST(ClassSim, DISABLED_TypeParameterReturnsAndInputsTakeTheActual) {
  SimFixture f;
  auto* design = ElaborateSrc(kTypeParameterSubroutineSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r1", 0u},
                    {"r2", 0u},
                    {"r3", 0u},
                    {"r4", 0u},
                    {"r5", 22136u},
                    {"r6", 160804u},
                    {"r7", 1u},
                    {"r8", 22136u},
                    {"r10", 22136u},
                    {"r11", 0u}});
}

const char* const kSpecializationPropertyNewSrc =
    "class PDef #(type T = byte, int size = 2);\n"
    "  T words[size];\n"
    "endclass\n"
    "class PDA #(type T = byte, int size = 2);\n"
    "  T words[size];\n"
    "  function new(int v); words[size-1] = v; endfunction\n"
    "endclass\n"
    "typedef PDef#(shortint, 5) P5;\n"
    "package pk;\n"
    "  class PMem #(type T = byte, int size = 2); T words[size]; endclass\n"
    "  class PH; PMem#(shortint, 5) held; function void fill(); held = new; "
    "endfunction endclass\n"
    "endpackage\n"
    "class ND #(int size); bit [15:0] words[size]; endclass\n"
    "class Base5; PDef#(shortint, 5) inh; endclass\n"
    "class Holder extends Base5;\n"
    "  PDef#(shortint, 5) held;\n"
    "  PDef#(shortint, 5) init = new;\n"
    "  P5 aliased;\n"
    "  static PDef#(shortint, 5) shared;\n"
    "  PDef#(shortint, 5) elems[2];\n"
    "  ND#(5) nd;\n"
    "  PDA#(shortint, 5) pa;\n"
    "  function void fill(); held = new; nd = new; inh = new; pa = "
    "new(16'h1234); endfunction\n"
    "  function new(); aliased = new; endfunction\n"
    "endclass\n"
    "module top;\n"
    "  class MH; PDef#(shortint, 5) held; function void fill(); held = new; "
    "endfunction endclass\n"
    "  Holder ho = new;\n"
    "  Holder hm = new;\n"
    "  MH mh = new;\n"
    "  pk::PH ph = new;\n"
    "  PDef#(shortint, 5) mv;\n"
    "  PDef#(shortint, 5) ma[2];\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14;\n"
    "  initial begin\n"
    "    ho.held = new; ho.held.words[4] = 16'h1234; r1 = ho.held.words[4];\n"
    "    hm.fill(); hm.held.words[4] = 16'h1234; r2 = hm.held.words[4];\n"
    "    ho.init.words[4] = 16'h1234; r3 = ho.init.words[4];\n"
    "    Holder::shared = new; Holder::shared.words[4] = 16'h1234; r4 = "
    "Holder::shared.words[4];\n"
    "    ho.elems[1] = new; ho.elems[1].words[4] = 16'h1234; r5 = "
    "ho.elems[1].words[4];\n"
    "    ph.fill(); ph.held.words[4] = 16'h1234; r6 = ph.held.words[4];\n"
    "    hm.nd.words[4] = 16'h1234; r7 = hm.nd.words[4];\n"
    "    hm.inh.words[4] = 16'h1234; r8 = hm.inh.words[4];\n"
    "    mh.fill(); mh.held.words[4] = 16'h1234; r9 = mh.held.words[4];\n"
    "    r10 = hm.pa.words[4];\n"
    "    ho.aliased.words[4] = 16'h1234; r11 = ho.aliased.words[4];\n"
    "    mv = new; mv.words[4] = 16'h1234; r12 = mv.words[4];\n"
    "    ma[1] = new; ma[1].words[4] = 16'h1234; r13 = ma[1].words[4];\n"
    "  end\n"
    "endmodule\n";

TEST(ClassSim,
     NewIntoATypedefPropertyOrAModuleVariableBuildsTheSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(kSpecializationPropertyNewSrc, f);
  LowerRunAndCheck(f, design, {{"r11", 4660u}, {"r12", 4660u}, {"r13", 4660u}});
}

TEST(ClassSim,
     DISABLED_NewIntoASpecializationPropertyBuildsThatSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(kSpecializationPropertyNewSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r1", 4660u},
                    {"r2", 4660u},
                    {"r3", 4660u},
                    {"r4", 4660u},
                    {"r5", 4660u},
                    {"r6", 4660u},
                    {"r7", 4660u},
                    {"r8", 4660u},
                    {"r9", 4660u},
                    {"r10", 4660u}});
}

const char* const kEnumerationParameterInEveryScopeSrc =
    "package pk;\n"
    "  class PT; typedef enum {A, B} e_t; parameter e_t P1 = B; localparam e_t "
    "L1 = B; parameter int K = B; endclass\n"
    "  class PI; parameter enum {G, H} PE = H; endclass\n"
    "  class PP #(parameter enum {X, Y} E = Y); endclass\n"
    "  class PQ #(enum {M, N} F = N); endclass\n"
    "  class PB; typedef enum logic [2:0] {Q = 3, R = 5} q_t; parameter q_t P4 "
    "= R; endclass\n"
    "endpackage\n"
    "class Outer;\n"
    "  class NT; typedef enum {A, B} e_t; parameter e_t P1 = B; localparam e_t "
    "L1 = B; parameter int K = B; endclass\n"
    "  class NI; parameter enum {G, H} PE = H; endclass\n"
    "  class NP #(parameter enum {X, Y} E = Y); endclass\n"
    "  class NQ #(enum {M, N} F = N); endclass\n"
    "  class NB; typedef enum logic [2:0] {Q = 3, R = 5} q_t; parameter q_t P4 "
    "= R; endclass\n"
    "endclass\n"
    "module top;\n"
    "  class MT; typedef enum {A, B} e_t; parameter e_t P1 = B; localparam e_t "
    "L1 = B; parameter int K = B; endclass\n"
    "  class MI; parameter enum {G, H} PE = H; endclass\n"
    "  class MP #(parameter enum {X, Y} E = Y); endclass\n"
    "  class MQ #(enum {M, N} F = N); endclass\n"
    "  class MB; typedef enum logic [2:0] {Q = 3, R = 5} q_t; parameter q_t P4 "
    "= R; endclass\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, "
    "r16, r17, r18;\n"
    "  initial begin\n"
    "    r1 = pk::PT::P1;\n"
    "    r2 = pk::PT::L1;\n"
    "    r3 = pk::PT::K;\n"
    "    r4 = pk::PI::PE;\n"
    "    r5 = pk::PP#()::E;\n"
    "    r6 = pk::PQ#()::F;\n"
    "    r7 = pk::PB::P4;\n"
    "    r8 = Outer::NT::P1 + Outer::NT::L1 * 10 + Outer::NT::K * 100;\n"
    "    r9 = Outer::NI::PE;\n"
    "    r10 = Outer::NP#()::E;\n"
    "    r11 = Outer::NQ#()::F;\n"
    "    r12 = Outer::NB::P4;\n"
    "    r13 = MT::P1 + MT::L1 * 10 + MT::K * 100;\n"
    "    r14 = MI::PE;\n"
    "    r15 = MP#()::E;\n"
    "    r16 = MQ#()::F;\n"
    "    r17 = MB::P4;\n"
    "  end\n"
    "endmodule\n";

TEST(ClassParamsSim, EnumerationParameterOfAPackageModuleOrNestedClassReads) {
  SimFixture f;
  auto* design = ElaborateSrc(kEnumerationParameterInEveryScopeSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 1u},
                    {"r4", 1u},
                    {"r7", 5u},
                    {"r8", 111u},
                    {"r12", 5u},
                    {"r13", 111u},
                    {"r14", 1u},
                    {"r17", 5u}});
}

TEST(ClassParamsSim,
     DISABLED_InPlaceEnumerationPortOfAPackageModuleOrNestedClassReads) {
  SimFixture f;
  auto* design = ElaborateSrc(kEnumerationParameterInEveryScopeSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r5", 1u},
                    {"r6", 1u},
                    {"r9", 1u},
                    {"r10", 1u},
                    {"r11", 1u},
                    {"r15", 1u},
                    {"r16", 1u}});
}

const char* const kTypeParameterByNameDefaultOrDerivedSrc =
    "class MemD #(type T = byte, int size = 1);\n"
    "  typedef T elem_t;\n"
    "  function T next(T a); return a + 1; endfunction\n"
    "  function T viaresult(T a); viaresult = a + 1; endfunction\n"
    "  function elem_t viatypedef(T a); return a + 1; endfunction\n"
    "  static function T snext(T a); return a + 1; endfunction\n"
    "  function T wide(); return 32'h12345678; endfunction\n"
    "  function int arg(T a); return a; endfunction\n"
    "  function void outs(output T o, inout T io, ref T r);\n"
    "    o = 32'h12345678; o = o >> 8;\n"
    "    io = 32'h12345678; io = io >> 8;\n"
    "    r = 32'h12345678; r = r >> 8;\n"
    "  endfunction\n"
    "  task targ(input T a, output int o); o = a; endtask\n"
    "endclass\n"
    "class Sub #(type U = byte) extends MemD #(U, 3);\n"
    "endclass\n"
    "module top;\n"
    "  MemD#(.T(shortint)) dn = new;\n"
    "  MemD dd = new;\n"
    "  Sub#(shortint) ds = new;\n"
    "  shortint so, sio, sr;\n"
    "  byte bo, bio, br;\n"
    "  shortint to, tio, tr;\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, "
    "r16, r17, r18, r19, r20, r21, r22, r23, r24, r25;\n"
    "  initial begin\n"
    "    r1 = dn.next(16'hFFFF);\n"
    "    r2 = dn.viaresult(16'hFFFF);\n"
    "    r3 = dn.viatypedef(16'hFFFF);\n"
    "    r4 = MemD#(.T(shortint))::snext(16'hFFFF);\n"
    "    r5 = dn.wide();\n"
    "    r6 = $bits(dn.next(1)) * 100 + $bits(dd.next(1)) * 10000 + "
    "$bits(ds.next(1));\n"
    "    r7 = dn.arg(32'h12345678);\n"
    "    r8 = dd.next(8'hFF);\n"
    "    r9 = dd.viaresult(8'hFF);\n"
    "    r10 = dd.viatypedef(8'hFF);\n"
    "    r11 = MemD#()::snext(8'hFF);\n"
    "    r12 = dd.wide();\n"
    "    r13 = dd.arg(32'h12345678);\n"
    "    r14 = ds.next(16'hFFFF);\n"
    "    r15 = ds.viaresult(16'hFFFF);\n"
    "    r16 = ds.viatypedef(16'hFFFF);\n"
    "    r17 = Sub#(shortint)::snext(16'hFFFF);\n"
    "    r18 = ds.wide();\n"
    "    r19 = ds.arg(32'h12345678);\n"
    "    dn.outs(so, sio, sr);\n"
    "    r20 = so * 10000 + sio * 100 + sr;\n"
    "    dd.outs(bo, bio, br);\n"
    "    r21 = bo * 10000 + bio * 100 + br;\n"
    "    ds.outs(to, tio, tr);\n"
    "    r22 = to * 10000 + tio * 100 + tr;\n"
    "    dn.targ(32'h12345678, r23);\n"
    "    dd.targ(32'h12345678, r24);\n"
    "    ds.targ(32'h12345678, r25);\n"
    "  end\n"
    "endmodule\n";

TEST(ClassSim, TypeParameterOutputsTakeTheActualByNameDefaultOrDerived) {
  SimFixture f;
  auto* design = ElaborateSrc(kTypeParameterByNameDefaultOrDerivedSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r20", 868686u}, {"r21", 0u}, {"r22", 868686u}});
}

TEST(
    ClassSim,
    DISABLED_TypeParameterReturnsAndInputsTakeTheActualByNameDefaultOrDerived) {
  SimFixture f;
  auto* design = ElaborateSrc(kTypeParameterByNameDefaultOrDerivedSrc, f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 0u},     {"r2", 0u},      {"r3", 0u},      {"r4", 0u},
       {"r5", 22136u}, {"r6", 81616u},  {"r7", 22136u},  {"r8", 0u},
       {"r9", 0u},     {"r10", 0u},     {"r11", 0u},     {"r12", 120u},
       {"r13", 120u},  {"r14", 0u},     {"r15", 0u},     {"r16", 0u},
       {"r17", 0u},    {"r18", 22136u}, {"r19", 22136u}, {"r23", 22136u},
       {"r24", 120u},  {"r25", 22136u}});
}

TEST(ClassSim,
     DISABLED_NewIntoASpecializationPropertyOfAModuleOrPackageClassBuildsIt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  class PDef #(type T = byte, int size = 2); T words[size]; endclass\n"
      "  class PDA #(type T = byte, int size = 2); T words[size]; function "
      "new(int v); words[size-1] = v; endfunction endclass\n"
      "  class PND #(int size); bit [15:0] words[size]; endclass\n"
      "  class PH; PDef#(shortint, 5) held; PDef#(shortint, 5) init = new; "
      "static PDef#(shortint, 5) shared;\n"
      "    PDef#(shortint, 5) elems[2]; PND#(5) nd; PDA#(shortint, 5) pa; "
      "PDef#(shortint, 5) mh;\n"
      "    function void fill(); held = new; nd = new; pa = new(16'h1234); "
      "endfunction\n"
      "  endclass\n"
      "  class PHD extends PH; function void fill2(); mh = new; endfunction "
      "endclass\n"
      "endpackage\n"
      "module top;\n"
      "  class MDef #(type T = byte, int size = 2); T words[size]; endclass\n"
      "  class MDA #(type T = byte, int size = 2); T words[size]; function "
      "new(int v); words[size-1] = v; endfunction endclass\n"
      "  class MND #(int size); bit [15:0] words[size]; endclass\n"
      "  class MH; MDef#(shortint, 5) held; MDef#(shortint, 5) init = new; "
      "static MDef#(shortint, 5) shared;\n"
      "    MDef#(shortint, 5) elems[2]; MND#(5) nd; MDA#(shortint, 5) pa; "
      "MDef#(shortint, 5) mh;\n"
      "    function void fill(); held = new; nd = new; pa = new(16'h1234); "
      "endfunction\n"
      "  endclass\n"
      "  class MHD extends MH; function void fill2(); mh = new; endfunction "
      "endclass\n"
      "  MH mo = new;\n"
      "  MH mm = new;\n"
      "  MHD md = new;\n"
      "  pk::PH po = new;\n"
      "  pk::PH pm = new;\n"
      "  pk::PHD pd = new;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14;\n"
      "  initial begin\n"
      "    mo.held = new; mo.held.words[4] = 16'h1234; r1 = mo.held.words[4];\n"
      "    mm.fill(); mm.held.words[4] = 16'h1234; r2 = mm.held.words[4];\n"
      "    mo.init.words[4] = 16'h1234; r3 = mo.init.words[4];\n"
      "    MH::shared = new; MH::shared.words[4] = 16'h1234; r4 = "
      "MH::shared.words[4];\n"
      "    mo.elems[1] = new; mo.elems[1].words[4] = 16'h1234; r5 = "
      "mo.elems[1].words[4];\n"
      "    mm.nd.words[4] = 16'h1234; r6 = mm.nd.words[4] + mm.pa.words[4] * "
      "0;\n"
      "    r7 = mm.pa.words[4];\n"
      "    md.fill2(); md.mh.words[4] = 16'h1234; r8 = md.mh.words[4];\n"
      "    po.held = new; po.held.words[4] = 16'h1234; r9 = po.held.words[4];\n"
      "    po.init.words[4] = 16'h1234; r10 = po.init.words[4];\n"
      "    pk::PH::shared = new; pk::PH::shared.words[4] = 16'h1234; r11 = "
      "pk::PH::shared.words[4];\n"
      "    po.elems[1] = new; po.elems[1].words[4] = 16'h1234; r12 = "
      "po.elems[1].words[4];\n"
      "    pm.fill(); r13 = pm.pa.words[4];\n"
      "    pd.fill2(); pd.mh.words[4] = 16'h1234; r14 = pd.mh.words[4];\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 4660u},
                    {"r2", 4660u},
                    {"r3", 4660u},
                    {"r4", 4660u},
                    {"r5", 4660u},
                    {"r6", 4660u},
                    {"r7", 4660u},
                    {"r8", 4660u},
                    {"r9", 4660u},
                    {"r10", 4660u},
                    {"r11", 4660u},
                    {"r12", 4660u},
                    {"r13", 4660u},
                    {"r14", 4660u}});
}

}  // namespace
