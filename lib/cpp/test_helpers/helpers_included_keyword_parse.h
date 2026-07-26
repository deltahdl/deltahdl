#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
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

  EXPECT_FALSE(ParseWithPreprocessorOk(InNoconfig(kSrc)));

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
