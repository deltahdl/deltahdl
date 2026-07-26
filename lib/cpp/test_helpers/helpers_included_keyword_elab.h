#pragma once

#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_keyword_version.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

// §22.14: each version_specifier's reserved word list includes the lists of
// the versions before it, so every word an earlier table introduced keeps its
// keyword role under a later specifier. The checks here state that as
// structure rather than as tokens -- a source written entirely in one included
// table's words is elaborated under the specifier `spec` names, and each
// declaration is looked for in the design as the kind that word makes it. A
// word that had quietly decayed into a plain identifier would still lex, so
// only the elaborated design settles it.
//
// One check per table, taking the specifier as its parameter: the table fixes
// what is written, the specifier fixes what is in force, and inclusion is the
// claim that the two go together for every specifier at or after the table's
// own version.

// Table 22-1, the Verilog-1995 list: the net types, the variable types with
// their widths and their four-state and real and event flags, a parameter, and
// a gate instantiation.
inline void ExpectTable221DeclarationsElaborate(const char* spec) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In(spec,
                                   "module m (input wire a, output wire y);\n"
                                   "  wand     wa;\n"
                                   "  wor      wo;\n"
                                   "  triand   ta;\n"
                                   "  trior    to;\n"
                                   "  tri0     t0;\n"
                                   "  tri1     t1;\n"
                                   "  trireg   tr;\n"
                                   "  supply0  gnd;\n"
                                   "  supply1  vdd;\n"
                                   "  reg [7:0] r;\n"
                                   "  integer   i;\n"
                                   "  real      rl;\n"
                                   "  time      tm;\n"
                                   "  event     ev;\n"
                                   "  parameter P = 8;\n"
                                   "  and g1 (y, a, a);\n"
                                   "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  struct NetCase {
    const char* name;
    NetType type;
  };
  const NetCase kNets[] = {
      {"wa", NetType::kWand},     {"wo", NetType::kWor},
      {"ta", NetType::kTriand},   {"to", NetType::kTrior},
      {"t0", NetType::kTri0},     {"t1", NetType::kTri1},
      {"tr", NetType::kTrireg},   {"gnd", NetType::kSupply0},
      {"vdd", NetType::kSupply1},
  };
  for (const auto& c : kNets) {
    const auto* n = FindNet(design, "m", c.name);
    ASSERT_NE(n, nullptr) << c.name;
    EXPECT_EQ(n->net_type, c.type) << c.name;
  }

  const auto* v = FindVar(design, "m", "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  v = FindVar(design, "m", "i");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);
  v = FindVar(design, "m", "rl");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);
  v = FindVar(design, "m", "tm");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);
  v = FindVar(design, "m", "ev");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);

  const auto* p = FindParam(design, "m", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 8);
}

// Table 22-2, the Verilog-2001 list, as structure rather than as tokens.
// `localparam` resolves to a constant, `genvar`/`generate`/`endgenerate`
// produce one copy of the loop body per iteration, and `signed`/`unsigned`
// select what they select. The three are tied together on purpose: the
// localparam is the loop bound, so the count of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
inline void ExpectTable222DeclarationsElaborate(const char* spec) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In(spec,
                                   "module t;\n"
                                   "  localparam L = 4;\n"
                                   "  genvar g;\n"
                                   "  reg signed   [7:0] s;\n"
                                   "  reg unsigned [7:0] u;\n"
                                   "  wire signed  [7:0] sn;\n"
                                   "  generate\n"
                                   "    for (g = 0; g < L; g = g + 1)\n"
                                   "      begin : blk\n"
                                   "        reg [7:0] slot;\n"
                                   "        if (g == 1) begin : only_one\n"
                                   "          reg [7:0] picked;\n"
                                   "        end\n"
                                   "      end\n"
                                   "  endgenerate\n"
                                   "endmodule\n"),
                                f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* l = FindParam(design, "t", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_localparam);
  EXPECT_EQ(l->resolved_value, 4);

  EXPECT_EQ(CountVarsEndingIn(design, "t", "slot"), 4u);
  EXPECT_EQ(CountVarsEndingIn(design, "t", "picked"), 1u);

  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_signed);
  const auto* u = FindVar(design, "t", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(u->is_signed);
  const auto* sn = FindNet(design, "t", "sn");
  ASSERT_NE(sn, nullptr);
  EXPECT_TRUE(sn->is_signed);
}

// Table 22-3, the Verilog-2005 list, whose lone entry is a net type of its
// own: `uwire` shall still resolve to itself, scalar and vectored alike.
inline void ExpectTable223DeclarationsElaborate(const char* spec) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In(spec,
                                              "module m;\n"
                                              "  uwire    uw;\n"
                                              "  uwire [7:0] uwv;\n"
                                              "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  for (const char* name : {"uw", "uwv"}) {
    const auto* n = FindNet(design, "m", name);
    ASSERT_NE(n, nullptr) << name;
    EXPECT_EQ(n->net_type, NetType::kUwire) << name;
  }
}
