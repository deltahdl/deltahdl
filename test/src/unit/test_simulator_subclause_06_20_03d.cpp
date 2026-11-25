#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

constexpr std::string_view kScopeTypeParameters =
    "package pk;\n"
    "  parameter type PT = shortint;\n"
    "  localparam type LT = byte;\n"
    "  PT pv = 70000;\n"
    "endpackage\n"
    "parameter type UT = shortint;\n"
    "class X #(type T = int); T v; static int s; endclass\n"
    "module m #(type T = int) (); T x; endmodule\n";

std::string WithScopeTypeParameters(std::string_view before,
                                    std::string_view items) {
  return std::string(kScopeTypeParameters) + std::string(before) +
         "module top;\n"
         "  int r1, r2, r3, r4, r5, r6, r7;\n" +
         std::string(items) + "endmodule\n";
}

TEST(ScopeTypeParameterSim, ModuleVariablesTakeItsType) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WithScopeTypeParameters("",
                                           "  pk::PT y = 70000;\n"
                                           "  pk::LT z;\n"
                                           "  typedef pk::PT tp;\n"
                                           "  tp w;\n"
                                           "  UT u;\n"
                                           "  parameter type T = pk::PT;\n"
                                           "  T x;\n"
                                           "  initial begin\n"
                                           "    r1 = y;\n"
                                           "    r2 = $bits(y);\n"
                                           "    r3 = $bits(z);\n"
                                           "    r4 = $bits(w);\n"
                                           "    r5 = $bits(u);\n"
                                           "    r6 = $bits(x);\n"
                                           "    r7 = pk::pv;\n"
                                           "  end\n"),
                   f);
  LowerRunAndCheck(f, design,
                   {{"r1", 4464u},
                    {"r2", 16u},
                    {"r3", 8u},
                    {"r4", 16u},
                    {"r5", 16u},
                    {"r6", 16u},
                    {"r7", 4464u}});
}

TEST(ScopeTypeParameterSim, ImportedNameTakesItsType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      WithScopeTypeParameters("module w; import pk::*; PT y; LT z;\n"
                              "  initial begin\n"
                              "    top.r1 = $bits(y);\n"
                              "    top.r2 = $bits(z);\n"
                              "  end\n"
                              "endmodule\n"
                              "module x; import pk::PT; PT y;\n"
                              "  initial top.r3 = $bits(y);\n"
                              "endmodule\n",
                              "  w a();\n"
                              "  x b();\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 16u}, {"r2", 8u}, {"r3", 16u}});
}

TEST(ScopeTypeParameterSim, SubroutineAndBlockLocalsTakeItsType) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WithScopeTypeParameters(
                       "",
                       "  task t(pk::PT a, output UT b); b = a; endtask\n"
                       "  function pk::LT g(int a); return a; endfunction\n"
                       "  initial begin\n"
                       "    pk::PT y;\n"
                       "    UT u;\n"
                       "    pk::LT z;\n"
                       "    y = 70000;\n"
                       "    u = 70000;\n"
                       "    z = 300;\n"
                       "    r1 = y;\n"
                       "    r2 = u;\n"
                       "    r3 = z;\n"
                       "    t(70000, r4);\n"
                       "    r5 = g(300);\n"
                       "  end\n"),
                   f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 4464u}, {"r2", 4464u}, {"r3", 44u}, {"r4", 4464u}, {"r5", 44u}});
}

TEST(ScopeTypeParameterSim, ClassPropertyTakesItsType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      WithScopeTypeParameters("class Q; pk::PT p; UT q; endclass\n",
                              "  Q h = new;\n"
                              "  initial begin\n"
                              "    h.p = 70000;\n"
                              "    r1 = h.p;\n"
                              "    r2 = $bits(h.p);\n"
                              "    r3 = $bits(h.q);\n"
                              "  end\n"),
      f);
  LowerRunAndCheck(f, design, {{"r1", 4464u}, {"r2", 16u}, {"r3", 16u}});
}

TEST(ScopeTypeParameterSim, TypeParameterSetToItTakesItsType) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WithScopeTypeParameters("",
                                           "  m #(pk::PT) a();\n"
                                           "  m #(.T(UT)) b();\n"
                                           "  X #(pk::PT) c = new;\n"
                                           "  X #(UT) d = new;\n"
                                           "  initial begin\n"
                                           "    X#(pk::PT)::s = 4;\n"
                                           "    X#(UT)::s = X#(UT)::s + 1;\n"
                                           "    X#(byte)::s = 9;\n"
                                           "    r1 = $bits(a.x);\n"
                                           "    r2 = $bits(b.x);\n"
                                           "    r3 = $bits(c.v);\n"
                                           "    r4 = $bits(d.v);\n"
                                           "    r5 = X#(shortint)::s;\n"
                                           "  end\n"),
                   f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 16u}, {"r2", 16u}, {"r3", 16u}, {"r4", 16u}, {"r5", 5u}});
}

TEST(ScopeTypeParameterSim, InterfaceProgramAndGenerateBlockTakeItsType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      WithScopeTypeParameters("interface i; pk::PT y; UT u; endinterface\n"
                              "program p; pk::PT y; UT u;\n"
                              "  initial begin\n"
                              "    top.r5 = $bits(y);\n"
                              "    top.r6 = $bits(u);\n"
                              "  end\n"
                              "endprogram\n",
                              "  i ii();\n"
                              "  p pp();\n"
                              "  if (1) begin : g\n"
                              "    pk::PT y;\n"
                              "    UT u;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    r1 = $bits(ii.y);\n"
                              "    r2 = $bits(ii.u);\n"
                              "    r3 = $bits(g.y);\n"
                              "    r4 = $bits(g.u);\n"
                              "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 16u},
                    {"r2", 16u},
                    {"r3", 16u},
                    {"r4", 16u},
                    {"r5", 16u},
                    {"r6", 16u}});
}

TEST(ScopeTypeParameterSim, QueryCastAndStructureMemberTakeItsType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      WithScopeTypeParameters(
          "",
          "  typedef struct packed { pk::PT a; UT b; } s_t;\n"
          "  if (type(UT) == type(shortint)) begin : g int z = 3; end\n"
          "  initial begin\n"
          "    r1 = $bits(UT);\n"
          "    r2 = $bits(pk::PT);\n"
          "    r3 = $bits(s_t);\n"
          "    r4 = pk::PT'(70000);\n"
          "    r5 = UT'(70000);\n"
          "    #1 r6 = g.z;\n"
          "  end\n"),
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 16u},
                    {"r2", 16u},
                    {"r3", 32u},
                    {"r4", 4464u},
                    {"r5", 4464u},
                    {"r6", 3u}});
}

TEST(ScopeTypeParameterSim, PackageTypeParameterNamesAClass) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WithScopeTypeParameters("package q;\n"
                                           "  class K; byte b; endclass\n"
                                           "  parameter type class CT = K;\n"
                                           "endpackage\n",
                                           "  q::CT h = new;\n"
                                           "  initial begin\n"
                                           "    h.b = 70;\n"
                                           "    r1 = h.b;\n"
                                           "  end\n"),
                   f);
  LowerRunAndCheck(f, design, {{"r1", 70u}});
}

}  // namespace
