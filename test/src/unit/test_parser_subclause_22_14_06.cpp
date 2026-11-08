#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_table_sweeps.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog1995Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2005",
                                      kVerilog1995KeywordSweepAtParse);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog2001Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2005",
                                      kVerilog2001AddedKeywordSweep);
}

TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesTheVerilog2005Word) {
  ExpectKeywordTableIsReservedAtParse("1800-2005",
                                      kVerilog2005AddedKeywordSweep);
  ExpectUwireStillOpensNetDeclarations("1800-2005");
}

TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2005",
                                      kSystemVerilog2005AddedKeywordSweep);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2005", {"wire", "generate", "uwire"},
      {"design element", "port", "instance", "task", "named block"});
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005UnlistedWordsFillEveryIdentifierPosition) {
  ExpectUnlistedWordsNameEveryEntity("1800-2005", {"checker", "let"});
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder("1364-2005", "1800-2005",
                               {"logic", "int", "bit"});

  auto named_module =
      ParseWithPreprocessor(In2005("module logic;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "logic");

  auto named_gate =
      ParseWithPreprocessor(In2005("module m (input wire a, output wire y);\n"
                                   "  and int (y, a, a);\n"
                                   "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "int");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsTypeEveryDeclarationForm) {
  auto with_initializer =
      ParseWithPreprocessor(InSv2005("module m;\n"
                                     "  int   counted = 21;\n"
                                     "  byte  stepped = 8'd1;\n"
                                     "  logic [7:0] held = 8'd0;\n"
                                     "endmodule\n"));
  ASSERT_NE(with_initializer.cu, nullptr);
  EXPECT_FALSE(with_initializer.has_errors);
  const char* const kInitialized[] = {"counted", "stepped", "held"};
  for (const char* name : kInitialized) {
    bool found = false;
    for (auto* item : with_initializer.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      EXPECT_NE(item->init_expr, nullptr) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  auto ansi_ports = ParseWithPreprocessor(
      InSv2005("module ch (input logic [7:0] a, input byte b, output int y);\n"
               "  assign y = a + b;\n"
               "endmodule\n"));
  ASSERT_NE(ansi_ports.cu, nullptr);
  EXPECT_FALSE(ansi_ports.has_errors);
  auto* ch = ansi_ports.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 3u);
  EXPECT_EQ(ch->ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ch->ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ch->ports[2].data_type.kind, DataTypeKind::kInt);

  auto non_ansi =
      ParseWithPreprocessor(InSv2005("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  logic  [7:0] y;\n"
                                     "  always_comb y = a + a;\n"
                                     "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* body_typed = non_ansi.cu->modules[0];
  ASSERT_EQ(body_typed->ports.size(), 2u);
  EXPECT_EQ(body_typed->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : body_typed->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  auto initialized =
      ParseWithPreprocessor(In2005("module m;\n  int counted = 21;\n"
                                   "endmodule\n"));
  ASSERT_NE(initialized.cu, nullptr);
  EXPECT_FALSE(initialized.has_errors);
  ASSERT_EQ(initialized.cu->modules.size(), 1u);
  bool named_by_an_undeclared_type = false;
  for (auto* item : initialized.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kVarDecl || item->name != "counted")
      continue;
    named_by_an_undeclared_type = true;
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
    EXPECT_EQ(item->data_type.type_name, "int");
    EXPECT_TRUE(item->type_name_undeclared_at_parse);
    EXPECT_NE(item->init_expr, nullptr);
  }
  EXPECT_TRUE(named_by_an_undeclared_type);

  auto ansi = ParseWithPreprocessor(
      In2005("module ch (input logic [7:0] a, output int y);\n"
             "  assign y = a;\n"
             "endmodule\n"));
  EXPECT_TRUE(ReportedError(ansi.diags, "expected ')', got identifier",
                            LineInRegion(1), "23.2.2.2"));

  auto in_body =
      ParseWithPreprocessor(In2005("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  logic  [7:0] y;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(in_body.diags, "expected ';', got '['",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  logic     [7:0] a;\n"
      "  bit       [7:0] b;\n"
      "  byte            c;\n"
      "  shortint        d;\n"
      "  int             e;\n"
      "  longint         f;\n"
      "  shortreal       g;\n"
      "  string          h;\n"
      "  chandle         i;\n"
      "  var logic [7:0] j;\n"
      "  const int       k = 5;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  struct TypedDecl {
    const char* name;
    DataTypeKind kind;
  };
  const TypedDecl kDecls[] = {
      {"a", DataTypeKind::kLogic},     {"b", DataTypeKind::kBit},
      {"c", DataTypeKind::kByte},      {"d", DataTypeKind::kShortint},
      {"e", DataTypeKind::kInt},       {"f", DataTypeKind::kLongint},
      {"g", DataTypeKind::kShortreal}, {"h", DataTypeKind::kString},
      {"i", DataTypeKind::kChandle},   {"j", DataTypeKind::kLogic},
      {"k", DataTypeKind::kInt},
  };
  for (const auto& d : kDecls) {
    bool found = false;
    for (auto* item : r.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != d.name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, d.kind) << d.name;
    }
    EXPECT_TRUE(found) << d.name;
  }

  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedAggregateWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum {IDLE, BUSY} state_t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  typedef union packed { logic [7:0] whole; pair_t split; } view_t;\n"
      "  byte_t  v;\n"
      "  state_t s;\n"
      "  pair_t  p;\n"
      "  view_t  u;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  for (const char* name : {"byte_t", "state_t", "pair_t", "view_t"}) {
    EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTypedef, name))
        << name;
  }
  for (const char* name : {"v", "s", "p", "u"}) {
    bool found = false;
    for (auto* item : items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got identifier",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing, SystemVerilog2005AddedProcessWordsOpenBlocks) {
  const std::string kSrc =
      "module m (input logic clk, input logic d, output logic q);\n"
      "  logic combo;\n"
      "  logic latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysCombBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysFFBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysLatchBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kFinalBlock), nullptr);

  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got '@'",
                            LineInRegion(5), "6.8"));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got 'if'",
                            LineInRegion(6), "6.8"));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got 'begin'",
                            LineInRegion(7), "6.8"));
  ASSERT_NE(before.cu, nullptr);
  bool read_as_a_named_type = false;
  for (auto* item : before.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.type_name == "logic") {
      read_as_a_named_type = true;
    }
  }
  EXPECT_TRUE(read_as_a_named_type);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedStatementWordsOpenStatements) {
  const std::string kSrc =
      "module m;\n"
      "  int  arr [0:3];\n"
      "  int  i;\n"
      "  int  total;\n"
      "  logic [1:0] sel;\n"
      "  function int twice(input int n);\n"
      "    return n + n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    do total = total + 1; while (total < 2);\n"
      "    foreach (arr[j]) total = total + 1;\n"
      "    for (i = 0; i < 4; i = i + 1) begin\n"
      "      if (i == 1) continue;\n"
      "      if (i == 3) break;\n"
      "    end\n"
      "    unique case (sel) 2'b01: total = 1; default: total = 0; endcase\n"
      "    priority case (sel) 2'b01: total = 2; default: total = 0; endcase\n"
      "    if (sel inside {2'b01, 2'b10}) total = twice(3);\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* init =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);

  auto has_kind = [](Stmt* block, StmtKind kind) {
    for (auto* s : block->stmts) {
      if (s != nullptr && s->kind == kind) return true;
    }
    return false;
  };
  EXPECT_TRUE(has_kind(init->body, StmtKind::kDoWhile));
  EXPECT_TRUE(has_kind(init->body, StmtKind::kForeach));

  auto* fn =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->name, "twice");

  auto before = ParseWithPreprocessor(In2005(kSrc));
  ASSERT_NE(before.cu, nullptr);
  ASSERT_EQ(before.cu->modules.size(), 1u);
  bool array_of_an_undeclared_type = false;
  for (auto* item : before.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kVarDecl || item->name != "arr") continue;
    array_of_an_undeclared_type = true;
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
    EXPECT_EQ(item->data_type.type_name, "int");
    EXPECT_TRUE(item->type_name_undeclared_at_parse);
    EXPECT_EQ(item->unpacked_dims.size(), 1u);
  }
  EXPECT_TRUE(array_of_an_undeclared_type);
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got '['",
                            LineInRegion(5), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedDesignElementWordsOpenElements) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "  modport source (output data);\n"
      "endinterface\n"
      "program prg;\n"
      "  initial begin end\n"
      "endprogram\n"
      "class base;\n"
      "  int v;\n"
      "  function new(); v = 1; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  virtual function void bump(); this.v = super.v + 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  logic [7:0] w;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "base");
  EXPECT_EQ(r.cu->classes[1]->name, "derived");

  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl),
      nullptr);

  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedVerificationWordsOpenConstructs) {
  const std::string kSrc =
      "module m (input logic clk, input logic req, input logic ack);\n"
      "  logic [7:0] count;\n"
      "  property p_handshake;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "  sequence s_pulse;\n"
      "    @(posedge clk) req;\n"
      "  endsequence\n"
      "  clocking cb @(posedge clk);\n"
      "    input req;\n"
      "  endclocking\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp_count: coverpoint count {\n"
      "      bins low  = {0};\n"
      "      bins high = {255};\n"
      "    }\n"
      "  endgroup\n"
      "  initial begin\n"
      "    assert (count == 8'd0);\n"
      "    fork\n"
      "      count = 8'd1;\n"
      "    join_none\n"
      "    fork\n"
      "      count = 8'd2;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p_handshake"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kSequenceDecl, "s_pulse"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kClockingBlock), nullptr);
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kCovergroupDecl, "cg"));

  auto before = ParseWithPreprocessor(In2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog1995WordsStillWork) {
  ExpectVerilog1995ConstructsParse("1800-2005");
}

TEST(CompilerDirectiveParsing, SystemVerilog2005IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1800-2005");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog2001WordsStillWork) {
  ExpectVerilog2001ConstructsParse("1800-2005");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2005LeavesUnlistedWordsAsIdentifiers) {
  const char* const kUnlisted[] = {"until", "let", "global", "nettype", "soft"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(InSv2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    auto typed = ParseWithPreprocessor(InSv2005(as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace
