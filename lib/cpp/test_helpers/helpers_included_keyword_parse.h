#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

inline void ExpectVerilog1995ConstructsParse(const char* spec) {
  auto r = ParseWithPreprocessor(
      In(spec,
         "module m (input wire a, inout wire b, output wire y);\n"
         "  wand   w;\n"
         "  trireg (small) cap;\n"
         "  supply0 gnd;\n"
         "  integer i;\n"
         "  real    rl;\n"
         "  time    t;\n"
         "  event   e;\n"
         "  reg [1:0] sel;\n"
         "  and  g1 (y, a, b);\n"
         "  nmos g2 (w, a, b);\n"
         "  initial begin\n"
         "    for (i = 0; i < 2; i = i + 1) rl = rl + 1.0;\n"
         "    repeat (2) t = t + 1;\n"
         "    while (i > 0) i = i - 1;\n"
         "    casez (sel)\n"
         "      2'b1?: i = 1;\n"
         "      default: i = 0;\n"
         "    endcase\n"
         "    -> e;\n"
         "  end\n"
         "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "w"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "i"));

  auto* gate = FindGateByKind(items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "g1");
  EXPECT_NE(FindGateByKind(items, GateKind::kNmos), nullptr);
}

inline void ExpectVerilog2001ConstructsParse(const char* spec) {
  auto r = ParseWithPreprocessor(
      In(spec,
         "module m (input wire a, output wire y);\n"
         "  localparam L = 2;\n"
         "  genvar g;\n"
         "  reg signed   [7:0] s;\n"
         "  reg unsigned [7:0] u;\n"
         "  generate\n"
         "    for (g = 0; g < L; g = g + 1) begin : blk\n"
         "      reg [7:0] slot;\n"
         "    end\n"
         "  endgenerate\n"
         "  function automatic [7:0] twice(input reg [7:0] n);\n"
         "    twice = n + n;\n"
         "  endfunction\n"
         "  assign y = a;\n"
         "  specify\n"
         "    pulsestyle_ondetect y;\n"
         "    pulsestyle_onevent y;\n"
         "    showcancelled y;\n"
         "    noshowcancelled y;\n"
         "    (a => y) = 1;\n"
         "  endspecify\n"
         "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kParamDecl, "L"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kGenerateFor), nullptr);
  EXPECT_NE(FindSpecifyBlock(items), nullptr);

  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "s") {
      EXPECT_TRUE(item->data_type.is_signed);
    }
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "u") {
      EXPECT_FALSE(item->data_type.is_signed);
    }
  }
}

inline void ExpectConfigurationWordsParse(const char* spec) {
  const std::string kSrc =
      "module top;\n"
      "endmodule\n"
      "config config_a;\n"
      "  design top;\n"
      "  default liblist blue green;\n"
      "  instance top.u1 liblist red;\n"
      "  cell m1 use lib.m2;\n"
      "endconfig\n";

  auto r = ParseWithPreprocessor(In(spec, kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  EXPECT_EQ(cfg->name, "config_a");
  EXPECT_EQ(cfg->rules.size(), 3u);

  auto dropped = ParseWithPreprocessor(InNoconfig(kSrc));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(3), "3.12.1"));

  EXPECT_TRUE(ParseWithPreprocessorOk(InNoconfig("module top;\nendmodule\n")));
}

inline void ExpectVerilog2005ConstructsParse(const char* spec) {
  auto r = ParseWithPreprocessor(In(spec,
                                    "module m (output uwire y);\n"
                                    "  uwire [3:0] resolved;\n"
                                    "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  EXPECT_EQ(r.cu->modules[0]->ports.back().data_type.kind,
            DataTypeKind::kUwire);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "resolved") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
    }
  }
}

inline void ExpectSystemVerilog2005DesignElementsParse(CompilationUnit* cu) {
  ASSERT_EQ(cu->packages.size(), 1u);
  EXPECT_EQ(cu->packages[0]->name, "pkg");
  ASSERT_EQ(cu->interfaces.size(), 1u);
  EXPECT_EQ(cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(cu->classes.size(), 1u);
  EXPECT_EQ(cu->classes[0]->name, "base");
}

inline void ExpectSystemVerilog2005TypesAndProcessesParse(
    const std::vector<ModuleItem*>& items) {
  for (const char* name : {"byte_t", "state_t", "pair_t"}) {
    EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTypedef, name))
        << name;
  }
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysCombBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysFFBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysLatchBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kFinalBlock), nullptr);
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p_handshake"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kSequenceDecl, "s_pulse"));
}

inline void ExpectSystemVerilog2005DataTypeKindsParse(
    const std::vector<ModuleItem*>& items) {
  struct TypedDecl {
    const char* name;
    DataTypeKind kind;
  };
  const TypedDecl kDecls[] = {
      {"as_bit", DataTypeKind::kBit},
      {"as_byte", DataTypeKind::kByte},
      {"as_shortint", DataTypeKind::kShortint},
      {"as_int", DataTypeKind::kInt},
      {"as_longint", DataTypeKind::kLongint},
      {"as_string", DataTypeKind::kString},
      {"as_chandle", DataTypeKind::kChandle},
  };
  for (const auto& d : kDecls) {
    bool found = false;
    for (auto* item : items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != d.name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, d.kind) << d.name;
    }
    EXPECT_TRUE(found) << d.name;
  }
}

inline void ExpectSystemVerilog2005SourceUnwritableBeforeSystemVerilog(
    const std::string& src) {
  auto before = ParseWithPreprocessor(In2005(src));
  EXPECT_TRUE(ReportedError(before.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

inline void ExpectSystemVerilog2005ConstructsParse(const char* spec) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "  modport source (output data);\n"
      "endinterface\n"
      "class base;\n"
      "  int v;\n"
      "  function new(); v = 1; endfunction\n"
      "endclass\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  import pkg::*;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY} state_t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  byte_t   wide;\n"
      "  state_t  phase;\n"
      "  pair_t   split;\n"
      "  bit      [7:0] as_bit;\n"
      "  byte     as_byte;\n"
      "  shortint as_shortint;\n"
      "  int      as_int;\n"
      "  longint  as_longint;\n"
      "  string   as_string;\n"
      "  chandle  as_chandle;\n"
      "  logic    combo;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) wide = {7'd0, d};\n"
      "  final begin end\n"
      "  property p_handshake;\n"
      "    @(posedge clk) d;\n"
      "  endproperty\n"
      "  sequence s_pulse;\n"
      "    @(posedge clk) d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    assert (as_int == 0);\n"
      "    foreach (as_string[j]) as_byte = 8'd0;\n"
      "    unique case (phase) IDLE: as_int = 1; default: as_int = 0; endcase\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In(spec, kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ExpectSystemVerilog2005DesignElementsParse(r.cu);
  auto& items = r.cu->modules[0]->items;
  ExpectSystemVerilog2005TypesAndProcessesParse(items);
  ExpectSystemVerilog2005DataTypeKindsParse(items);
  ExpectSystemVerilog2005SourceUnwritableBeforeSystemVerilog(kSrc);
}

inline void ExpectKeywordTableIsReservedAtParse(const char* spec,
                                                const KeywordTableSweep& t) {
  EXPECT_EQ(t.count, t.expected_count) << t.what;
  size_t swept = 0;
  for (size_t i = 0; i < t.count; ++i) {
    const char* word = t.words[i];
    if (t.skip != nullptr && t.skip(word)) continue;
    ++swept;

    auto reserved = ParseWithPreprocessor(In(spec, VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        reserved.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is listed in " << t.what << " and is reserved here";

    for (const char* earlier : t.earlier) {
      if (earlier == nullptr) continue;
      auto freed = ParseWithPreprocessor(In(earlier, VarDecl(word)));
      ASSERT_NE(freed.cu, nullptr) << t.what << ' ' << word;
      EXPECT_FALSE(freed.has_errors) << t.what << ' ' << word;
      ASSERT_EQ(freed.cu->modules.size(), 1u) << t.what << ' ' << word;
      EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                   ModuleItemKind::kVarDecl, word))
          << word << " is free under " << earlier;
    }
  }
  EXPECT_EQ(swept, t.expected_swept) << t.what;
}

inline void ExpectFreedWordNamesModuleAndPorts(ModuleDecl* m) {
  EXPECT_EQ(m->name, "bit");
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "logic");
  EXPECT_EQ(m->ports[1].name, "byte");
}

inline void ExpectFreedWordsNameModuleDeclarations(
    const std::vector<ModuleItem*>& items) {
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kParamDecl, "int"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "string"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "longint"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "shortint"));
}

inline void ExpectFreedWordNamesInstance(
    const std::vector<ModuleItem*>& items) {
  auto* u = FindItemByKind(items, ModuleItemKind::kModuleInst);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->inst_module, "bit");
  EXPECT_EQ(u->inst_name, "interface");
}

inline void ExpectFreedWordsNameDeclaredEntities(const char* spec) {
  auto r = ParseWithPreprocessor(
      In(spec,
         "module bit (input wire logic, output wire byte);\n"
         "  parameter int = 4;\n"
         "  wire [7:0] string;\n"
         "  reg  [7:0] longint;\n"
         "  task shortint; begin longint = 8'd9; end endtask\n"
         "  initial begin : local\n"
         "    shortint;\n"
         "  end\n"
         "  assign byte = logic;\n"
         "endmodule\n"
         "module top;\n"
         "  wire a, b;\n"
         "  bit interface (.logic(a), .byte(b));\n"
         "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);

  ExpectFreedWordNamesModuleAndPorts(r.cu->modules[0]);
  ExpectFreedWordsNameModuleDeclarations(r.cu->modules[0]->items);
  ExpectFreedWordNamesInstance(r.cu->modules[1]->items);
}

inline void ExpectFreedWordIsAnOperandAndAssignmentTarget(const char* spec) {
  auto r = ParseWithPreprocessor(In(spec,
                                    "module m;\n"
                                    "  reg [7:0] logic;\n"
                                    "  reg [7:0] result;\n"
                                    "  initial begin\n"
                                    "    logic = 8'd5;\n"
                                    "    result = logic + 8'd1;\n"
                                    "  end\n"
                                    "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* first = NthInitialStmt(r, 0);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(first->lhs, nullptr);
  EXPECT_EQ(first->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(first->lhs->text, "logic");

  auto* second = NthInitialStmt(r, 1);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(second->rhs, nullptr);
  EXPECT_EQ(second->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(second->rhs->lhs, nullptr);
  EXPECT_EQ(second->rhs->lhs->text, "logic");
}

inline void ExpectConfigurationWordsNameVariablesAtParse() {
  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    auto dropped = ParseWithPreprocessor(InNoconfig(VarDecl(word)));
    ASSERT_NE(dropped.cu, nullptr) << word;
    EXPECT_FALSE(dropped.has_errors) << word;
    EXPECT_TRUE(HasItemKindNamed(dropped.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " names a variable under the configuration-free list";
  }
}

inline void ExpectUwireStillOpensNetDeclarations(const char* spec) {
  auto as_net = ParseWithPreprocessor(
      In(spec,
         "module m (input wire [7:0] a, output uwire [7:0] y);\n"
         "  uwire [3:0] vector_net;\n"
         "  assign y = a;\n"
         "endmodule\n"));
  ASSERT_NE(as_net.cu, nullptr);
  EXPECT_FALSE(as_net.has_errors);
  auto* m = as_net.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].data_type.kind, DataTypeKind::kUwire);
  bool net_seen = false;
  for (auto* item : m->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "vector_net") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
      net_seen = true;
    }
  }
  EXPECT_TRUE(net_seen);
}
