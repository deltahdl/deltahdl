#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

inline void ExpectVerilog1995NetTypesElaborate(RtlirDesign* design) {
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
}

inline void ExpectVerilog1995VariableTypesElaborate(RtlirDesign* design) {
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
}

inline void ExpectVerilog1995DeclarationsElaborate(const char* spec) {
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

  ExpectVerilog1995NetTypesElaborate(design);
  ExpectVerilog1995VariableTypesElaborate(design);

  const auto* p = FindParam(design, "m", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 8);
}

inline void ExpectVerilog2001SignQualifiersElaborate(RtlirDesign* design) {
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

inline void ExpectVerilog2001DeclarationsElaborate(const char* spec) {
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

  ExpectVerilog2001SignQualifiersElaborate(design);
}

inline void ExpectVerilog2005DeclarationsElaborate(const char* spec) {
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

inline void ExpectSystemVerilog2005DataTypesElaborate(RtlirDesign* design) {
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
}

inline void ExpectSystemVerilog2005EnumMembersElaborate(RtlirDesign* design) {
  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  auto members = m->enum_types.find("state_t");
  ASSERT_NE(members, m->enum_types.end());
  ASSERT_EQ(members->second.size(), 3u);
  EXPECT_EQ(members->second[0].name, "IDLE");
  EXPECT_EQ(members->second[0].value, 0);
  EXPECT_EQ(members->second[2].name, "DONE");
  EXPECT_EQ(members->second[2].value, 2);
}

inline void ExpectSystemVerilog2005ProcessesElaborate(RtlirDesign* design) {
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysComb));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysFF));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysLatch));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kFinal));
}

inline void ExpectSystemVerilog2005DesignElementsElaborate(
    RtlirDesign* design) {
  EXPECT_EQ(design->packages.size(), 1u);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool wildcard_import_seen = false;
  for (const auto& imp : m->imports) {
    if (imp.package_name == "pkg" && imp.is_wildcard)
      wildcard_import_seen = true;
  }
  EXPECT_TRUE(wildcard_import_seen);

  const auto* ifc = FindModule(design, "ifc");
  ASSERT_NE(ifc, nullptr);
  EXPECT_TRUE(ifc->is_interface);
}

inline void ExpectSystemVerilog2005SourceRejectedUnderVerilog2005(
    const std::string& src) {
  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In2005(src), included, "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected top-level declaration", LineInRegion(1),
                            "3.12.1"));
}

inline void ExpectSystemVerilog2005DeclarationsElaborate(const char* spec) {
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

  ExpectSystemVerilog2005DataTypesElaborate(design);
  ExpectSystemVerilog2005EnumMembersElaborate(design);
  ExpectSystemVerilog2005ProcessesElaborate(design);
  ExpectSystemVerilog2005DesignElementsElaborate(design);
  ExpectSystemVerilog2005SourceRejectedUnderVerilog2005(kSrc);
}

inline void ExpectLetDeclarationsElaborated(RtlirDesign* design) {
  bool cu_let_seen = false;
  for (auto* item : design->cu_let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "gain") {
      cu_let_seen = true;
    }
  }
  EXPECT_TRUE(cu_let_seen);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool module_let_seen = false;
  for (auto* item : m->let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "sum") {
      ASSERT_EQ(item->func_args.size(), 2u);
      EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kImplicit);
      EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
      module_let_seen = true;
    }
  }
  EXPECT_TRUE(module_let_seen);
}
