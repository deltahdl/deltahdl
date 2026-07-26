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

  // The two variables differ in nothing but the qualifier, so the declared
  // width is read back alongside the signedness: what the keyword selects is
  // the signedness and not the storage.
  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->width, 8u);
  EXPECT_TRUE(s->is_signed);
  const auto* u = FindVar(design, "t", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u);
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
                                              "  uwire       uw;\n"
                                              "  uwire [7:0] uwv;\n"
                                              "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  struct UwireCase {
    const char* name;
    uint32_t width;
  };
  for (const auto& c : {UwireCase{"uw", 1}, UwireCase{"uwv", 8}}) {
    const auto* n = FindNet(design, "m", c.name);
    ASSERT_NE(n, nullptr) << c.name;
    EXPECT_EQ(n->net_type, NetType::kUwire) << c.name;
    EXPECT_EQ(n->width, c.width) << c.name;
  }
}

// Table 22-4, the SystemVerilog-2005 list, read back as elaborated structure:
// the design elements beyond the module, the data types with their widths and
// four-state flags, the user-defined types with their resolved members, and
// the inferred processes each as its own kind. The closing leg is the same
// source under "1364-2005", the last specifier before this table, where none
// of it elaborates.
inline void ExpectTable224DeclarationsElaborate(const char* spec) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  import pkg::*;\n"
      "  ifc u_if();\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;\n"
      "  byte_t    wide;\n"
      "  state_t   phase;\n"
      "  logic     [7:0] as_logic;\n"
      "  bit       [7:0] as_bit;\n"
      "  byte            as_byte;\n"
      "  shortint        as_shortint;\n"
      "  int             as_int;\n"
      "  longint         as_longint;\n"
      "  string          as_string;\n"
      "  chandle         as_chandle;\n"
      "  var logic [3:0] as_var;\n"
      "  reg       [7:0] as_reg;\n"
      "  logic     combo;\n"
      "  logic     latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In(spec, kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  struct TypedVar {
    const char* name;
    uint32_t width;
    bool four_state;
  };
  const TypedVar kVars[] = {
      {"as_logic", 8, true}, {"as_bit", 8, false},
      {"as_byte", 8, false}, {"as_shortint", 16, false},
      {"as_int", 32, false}, {"as_longint", 64, false},
      {"as_var", 4, true},   {"as_reg", 8, true},
      {"wide", 8, true},     {"phase", 2, true},
  };
  for (const auto& c : kVars) {
    const auto* v = FindVar(design, "m", c.name);
    ASSERT_NE(v, nullptr) << c.name;
    EXPECT_EQ(v->width, c.width) << c.name;
    EXPECT_EQ(v->is_4state, c.four_state) << c.name;
  }

  const auto* s = FindVar(design, "m", "as_string");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_string);
  const auto* h = FindVar(design, "m", "as_chandle");
  ASSERT_NE(h, nullptr);
  EXPECT_TRUE(h->is_chandle);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  auto members = m->enum_types.find("state_t");
  ASSERT_NE(members, m->enum_types.end());
  ASSERT_EQ(members->second.size(), 3u);
  EXPECT_EQ(members->second[0].name, "IDLE");
  EXPECT_EQ(members->second[0].value, 0);
  EXPECT_EQ(members->second[2].name, "DONE");
  EXPECT_EQ(members->second[2].value, 2);

  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysComb));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysFF));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysLatch));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kFinal));

  EXPECT_EQ(design->packages.size(), 1u);
  bool wildcard_import_seen = false;
  for (const auto& imp : m->imports) {
    if (imp.package_name == "pkg" && imp.is_wildcard)
      wildcard_import_seen = true;
  }
  EXPECT_TRUE(wildcard_import_seen);
  const auto* ifc = FindModule(design, "ifc");
  ASSERT_NE(ifc, nullptr);
  EXPECT_TRUE(ifc->is_interface);

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}
