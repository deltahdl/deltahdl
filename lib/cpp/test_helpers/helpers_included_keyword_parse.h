#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"
#include "parser/ast.h"

using namespace delta;

// §22.14: each version_specifier's reserved word list includes the lists of
// the versions before it, so every construct an earlier table's words open
// stays writable under a later specifier. The checks here state that at the
// parse stage -- a source written in one included table's words is parsed
// under the specifier `spec` names, and the constructs those words exist to
// open are looked for in the syntax tree. Reserving a word is only half the
// claim; a word that stayed reserved but stopped opening its construct would
// pass a reservation sweep and fail here.
//
// One check per table, taking the specifier as its parameter: the table fixes
// what is written, the specifier fixes what is in force, and inclusion is the
// claim that the two go together for every specifier at or after the table's
// own version.

// Table 22-1, the Verilog-1995 list, in its keyword role: the resolved net
// types and drive strengths, the variable types, the gate primitives building
// structure, and the procedural statements building control flow.
inline void ExpectTable221ConstructsParse(const char* spec) {
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

// Table 22-2, the Verilog-2001 list, in its keyword role: `localparam`
// declares a constant, `genvar`/`generate`/`endgenerate` build a loop generate
// construct, `automatic` qualifies a subroutine, `signed` and `unsigned`
// qualify declarations, and the four pulse-control words are specify items --
// each the construct its word exists to open.
inline void ExpectTable222ConstructsParse(const char* spec) {
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

// The other half of Table 22-2: the ten words a configuration is written with,
// which is what separates that list from the configuration-free companion list
// published alongside it. Seven of them appear here and the declaration is
// built, while under the companion specifier the very same source cannot be
// written -- so a specifier that reaches this check inherits the full list
// rather than the reduced one. The module alongside the configuration parses
// under both, which is what keeps the rejection attributable to the
// configuration rather than to the source as a whole.
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
  // One rule per clause below the design statement: the default liblist, the
  // instance rule, and the cell rule.
  EXPECT_EQ(cfg->rules.size(), 3u);

  // The companion list leaves `config` an ordinary identifier, so the
  // declaration heading line 3 of the source above is no top-level declaration
  // at all and Parser::ParseTopLevel says so at src/parser/parser.cpp:499.
  auto dropped = ParseWithPreprocessor(InNoconfig(kSrc));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(3), "3.12.1"));

  EXPECT_TRUE(ParseWithPreprocessorOk(InNoconfig("module top;\nendmodule\n")));
}

// Table 22-3, the Verilog-2005 list, whose lone entry is a net type of its
// own: `uwire` shall still open a net declaration and type a port.
inline void ExpectTable223ConstructsParse(const char* spec) {
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

// Table 22-4, the SystemVerilog-2005 list, the largest thing a later specifier
// inherits: the design elements beyond the module, the data types with their
// kinds, the user-defined types, the inferred process forms, and the
// verification vocabulary. The closing leg is the same source under
// "1364-2005", the last specifier before this table, where none of it can be
// written -- which is what keeps the accepting leg from being any parse that
// happens to succeed.
inline void ExpectTable224ConstructsParse(const char* spec) {
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

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "base");

  auto& items = r.cu->modules[0]->items;
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

  // "1364-2005" reserves none of the words the source above is written in, so
  // `package` on its first line heads no top-level declaration and
  // Parser::ParseTopLevel says so at src/parser/parser.cpp:499.
  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

// The reserving half at this stage, table by table. Every entry of `t` is put
// in a declaration's identifier slot and rejected under `spec`, and -- where an
// earlier specifier leaves the entry free -- the same declaration is parsed
// there and read back off the tree as the variable declaration it spells.
// Reading it back is what keeps the accepting leg from being any parse that
// happens to succeed.
inline void ExpectKeywordTableIsReservedAtParse(const char* spec,
                                                const KeywordTableSweep& t) {
  EXPECT_EQ(t.count, t.expected_count) << t.what;
  size_t swept = 0;
  for (size_t i = 0; i < t.count; ++i) {
    const char* word = t.words[i];
    if (t.skip != nullptr && t.skip(word)) continue;
    ++swept;

    // VarDecl heads its declaration with `reg`, so the list is a variable
    // declaration and Parser::ParseVarDeclList reads the name under §6.8 --
    // the choice against §6.7 is made at src/parser/parser_types.cpp:568.
    // The report names the entry itself, because ParseDataType takes the
    // signing before the packed dimensions at
    // src/parser/parser_types.cpp:430 and so consumes nothing after `[7:0]`.
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

// A word no list in force reserves is an ordinary identifier, so it can name
// anything an identifier names. Declarations are only the most obvious
// position: this runs words a later standard reserves through the module name,
// both port names, a parameter, a net, a variable, a task, a named block, and
// an instance name, and reads each back off the parsed tree.
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

  auto* m = r.cu->modules[0];
  EXPECT_EQ(m->name, "bit");
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "logic");
  EXPECT_EQ(m->ports[1].name, "byte");
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kParamDecl, "int"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kNetDecl, "string"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kVarDecl, "longint"));
  EXPECT_TRUE(
      HasItemKindNamed(m->items, ModuleItemKind::kTaskDecl, "shortint"));

  auto* u =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->inst_module, "bit");
  EXPECT_EQ(u->inst_name, "interface");
}

// The same freed word as an expression operand and as the target of a
// procedural assignment -- positions that carry a value rather than introduce a
// name, and so reach the parser by a different path than a declaration does.
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

// The ten words on which the two lists published for the same Verilog standard
// disagree: each names a variable under the companion list that drops them,
// which is what shows a version that inherits "1364-2001" inherits the full
// list rather than the shorter one.
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

// Table 22-3's word in the keyword role it exists for: `uwire` still opens a
// net declaration and types a port under `spec`, which is what makes the
// inclusion about the role surviving rather than only about the identifier
// slot closing.
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
