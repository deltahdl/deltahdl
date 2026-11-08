#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_table_sweeps.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

constexpr const char* kItemsDoNotParse =
    "the constraint block's items do not parse from here";

struct SoftTally {
  size_t blocks = 0;
  size_t relations = 0;
  size_t dists = 0;
  size_t refs = 0;
  size_t discarded = 0;
};

SoftTally TallySoft(const ParseResult& r, const char* expected_var) {
  SoftTally t;
  for (auto* member : r.cu->classes[0]->members) {
    if (member->kind != ClassMemberKind::kConstraint) continue;
    ++t.blocks;
    t.relations += member->constraint_soft_exprs.size();
    t.dists += member->constraint_soft_dist_refs.size();
    t.refs += member->constraint_soft_refs.size();
    t.discarded += member->constraint_disable_soft_refs.size();
    for (const auto& ref : member->constraint_soft_refs)
      EXPECT_EQ(ref.name, expected_var);
    for (const auto& ref : member->constraint_disable_soft_refs)
      EXPECT_EQ(ref.name, expected_var);
  }
  return t;
}

TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryIncludedKeyword) {
  for (const auto& table :
       {kVerilog1995KeywordSweepAtParse, kVerilog2001AddedKeywordSweep,
        kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
        kSystemVerilog2009AddedKeywordSweep}) {
    ExpectKeywordTableIsReservedAtParse("1800-2012", table);
  }

  ExpectConfigurationWordsNameVariablesAtParse();
}

TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2012",
                                      kSystemVerilog2012AddedKeywordSweep);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2012", {"wire", "generate", "uwire", "logic", "until"});
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder(
      "1800-2009", "1800-2012",
      {"implements", "interconnect", "nettype", "soft"});

  auto named_module =
      ParseWithPreprocessor(In("1800-2009", "module soft;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "soft");

  auto named_gate =
      ParseWithPreprocessor(In("1800-2009",
                               "module m (input wire a, output wire y);\n"
                               "  and nettype (y, a, a);\n"
                               "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "nettype");
}

TEST(CompilerDirectiveParsing, SystemVerilog2012AddedImplementsOpensAClause) {
  const std::string kSrc =
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class base;\n"
      "  int held;\n"
      "endclass\n"
      "class port_t extends base implements reader, writer;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  const ClassDecl* impl = nullptr;
  for (auto* c : r.cu->classes) {
    if (c->name == "port_t") impl = c;
    if (c->name == "reader" || c->name == "writer")
      EXPECT_TRUE(c->is_interface);
  }
  ASSERT_NE(impl, nullptr);
  ASSERT_EQ(impl->implements_types.size(), 2u);
  EXPECT_EQ(impl->implements_types[0].name, "reader");
  EXPECT_EQ(impl->implements_types[1].name, "writer");
  EXPECT_EQ(impl->base_class, "base");

  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ';', got identifier",
                            LineInRegion(10), "8.3"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedInterconnectOpensNetsAndPorts) {
  const std::string kSrc =
      "module m (interconnect [3:0] p, input wire a, output wire y);\n"
      "  interconnect          scalar_ic;\n"
      "  interconnect [7:0]    bus_ic;\n"
      "  interconnect signed [7:0] signed_ic;\n"
      "  wire         [7:0]    plain;\n"
      "  assign y = a;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 3u);
  EXPECT_TRUE(m->ports[0].data_type.is_interconnect);
  EXPECT_TRUE(m->ports[0].data_type.is_net);
  EXPECT_FALSE(m->ports[1].data_type.is_interconnect);

  size_t marked = 0;
  for (auto* item : m->items) {
    if (item->kind != ModuleItemKind::kNetDecl) continue;
    if (item->name == "plain") {
      EXPECT_FALSE(item->data_type.is_interconnect);
      continue;
    }
    EXPECT_TRUE(item->data_type.is_interconnect) << item->name;
    if (item->name == "signed_ic") EXPECT_TRUE(item->data_type.is_signed);
    if (item->name == "bus_ic") EXPECT_FALSE(item->data_type.is_signed);
    ++marked;
  }
  EXPECT_EQ(marked, 3u);

  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ')', got identifier",
                            LineInRegion(1), "23.2.2.1"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedInterconnectTakesQualifiers) {
  const std::string kPorts =
      "module m (input interconnect [3:0] a, output interconnect [7:0] b,\n"
      "          inout interconnect c);\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kPorts));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  const Direction kDirections[] = {Direction::kInput, Direction::kOutput,
                                   Direction::kInout};
  for (size_t i = 0; i < ports.size(); ++i) {
    EXPECT_TRUE(ports[i].data_type.is_interconnect) << ports[i].name;
    EXPECT_EQ(ports[i].direction, kDirections[i]) << ports[i].name;
  }
  auto included = ParseWithPreprocessor(In("1800-2009", kPorts));
  EXPECT_TRUE(ReportedError(included.diags, "expected ')', got identifier",
                            LineInRegion(1), "23.2.2.2"));

  const std::string kUnsigned =
      "module m;\n"
      "  interconnect unsigned [3:0] q;\n"
      "endmodule\n";
  auto u = ParseWithPreprocessor(In("1800-2012", kUnsigned));
  ASSERT_NE(u.cu, nullptr);
  EXPECT_FALSE(u.has_errors);
  for (auto* item : u.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNetDecl) continue;
    EXPECT_TRUE(item->data_type.is_interconnect);
    EXPECT_FALSE(item->data_type.is_signed);
  }
  auto included_unsigned = ParseWithPreprocessor(In("1800-2009", kUnsigned));
  EXPECT_TRUE(ReportedError(included_unsigned.diags,
                            "expected ';', got 'unsigned'", LineInRegion(2),
                            "6.8"));
}

TEST(CompilerDirectiveParsing, SystemVerilog2012AddedNettypeOpensDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  function automatic real resolve_sum(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype real        analog_net with resolve_sum;\n"
      "  byte_net   bn;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  size_t nettypes = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNettypeDecl) continue;
    ++nettypes;
    if (item->name == "byte_net") {
      EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kLogic);
      EXPECT_TRUE(item->nettype_resolve_func.empty());
    }
    if (item->name == "analog_net") {
      EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kReal);
      EXPECT_EQ(item->nettype_resolve_func, "resolve_sum");
    }
  }
  EXPECT_EQ(nettypes, 2u);

  auto typeless = ParseWithPreprocessor(
      In("1800-2012", "module m;\n  nettype lone;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(typeless.diags,
                            "nettype declaration requires an explicit data "
                            "type",
                            LineInRegion(2), "6.6.7"));

  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ';', got 'logic'",
                            LineInRegion(5), "6.8"));
}

TEST(CompilerDirectiveParsing, SystemVerilog2012AddedNettypeTakesEveryForm) {
  const std::string kScoped =
      "package pkg;\n"
      "  function automatic real res(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  nettype real analog_net with pkg::res;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kScoped));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* scoped =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kNettypeDecl);
  ASSERT_NE(scoped, nullptr);
  EXPECT_EQ(scoped->name, "analog_net");
  EXPECT_EQ(scoped->nettype_resolve_func, "res");
  auto included_scoped = ParseWithPreprocessor(In("1800-2009", kScoped));
  EXPECT_TRUE(ReportedError(included_scoped.diags, "expected ';', got 'real'",
                            LineInRegion(7), "6.8"));

  const std::string kInPackage =
      "package pkg;\n"
      "  nettype logic [7:0] byte_net;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n";
  auto pk = ParseWithPreprocessor(In("1800-2012", kInPackage));
  ASSERT_NE(pk.cu, nullptr);
  ASSERT_EQ(pk.cu->packages.size(), 1u);
  EXPECT_FALSE(pk.has_errors);
  EXPECT_TRUE(HasItemKindNamed(pk.cu->packages[0]->items,
                               ModuleItemKind::kNettypeDecl, "byte_net"));
  auto included_pkg = ParseWithPreprocessor(In("1800-2009", kInPackage));
  EXPECT_TRUE(ReportedError(included_pkg.diags, "expected ';', got 'logic'",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedSoftQualifiesUnionsAndConstraints) {
  const std::string kUnion =
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  typedef union      { logic [7:0] c; logic [7:0] d; } plain_t;\n"
      "  overlay_t u;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kUnion));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  size_t typedefs = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    ++typedefs;
    if (item->name == "overlay_t") EXPECT_TRUE(item->typedef_type.is_soft);
    if (item->name == "plain_t") EXPECT_FALSE(item->typedef_type.is_soft);
  }
  EXPECT_EQ(typedefs, 2u);
  auto included_union = ParseWithPreprocessor(In("1800-2009", kUnion));
  EXPECT_TRUE(ReportedError(included_union.diags,
                            "union declarations may not have a tag before '{'",
                            LineInRegion(2), "7.2"));

  auto both = ParseWithPreprocessor(
      In("1800-2012",
         "module m;\n"
         "  typedef union soft tagged { logic [7:0] a; } both_t;\n"
         "endmodule\n"));
  EXPECT_TRUE(ReportedError(both.diags,
                            "union may have at most one of 'soft' or 'tagged'",
                            LineInRegion(2), "7.2"));

  const std::string kConstraint =
      "class c;\n"
      "  rand int v;\n"
      "  rand int w;\n"
      "  constraint cc { soft v == 43; w > 0; }\n"
      "  constraint dd { disable soft v; v == 7; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";

  auto cr = ParseWithPreprocessor(In("1800-2012", kConstraint));
  ASSERT_NE(cr.cu, nullptr);
  EXPECT_FALSE(cr.has_errors);
  ASSERT_EQ(cr.cu->classes.size(), 1u);
  auto here = TallySoft(cr, "v");
  EXPECT_EQ(here.blocks, 2u);
  EXPECT_EQ(here.relations, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.discarded, 1u);

  auto included = ParseWithPreprocessor(In("1800-2009", kConstraint));
  EXPECT_TRUE(ReportedError(included.diags, kItemsDoNotParse, LineInRegion(4),
                            "A.1.10"));
  EXPECT_TRUE(ReportedError(included.diags, kItemsDoNotParse, LineInRegion(5),
                            "A.1.10"));
  ASSERT_NE(included.cu, nullptr);
  ASSERT_EQ(included.cu->classes.size(), 1u);
  auto there = TallySoft(included, "v");
  EXPECT_EQ(there.blocks, 2u);
  EXPECT_EQ(there.relations, 0u) << "an ordinary identifier qualifies nothing";
  EXPECT_EQ(there.refs, 0u);
  EXPECT_EQ(there.discarded, 0u) << "and discards nothing";
}

TEST(CompilerDirectiveParsing, SystemVerilog2012AddedSoftTakesEveryPosition) {
  const std::string kDirectUnion =
      "module m;\n"
      "  union soft { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n";
  auto r = ParseWithPreprocessor(In("1800-2012", kDirectUnion));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* u_decl =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(u_decl, nullptr);
  EXPECT_EQ(u_decl->name, "u");
  EXPECT_TRUE(u_decl->data_type.is_soft);
  auto included = ParseWithPreprocessor(In("1800-2009", kDirectUnion));
  EXPECT_TRUE(ReportedError(included.diags,
                            "union declarations may not have a tag before '{'",
                            LineInRegion(2), "7.2"));

  const std::string kSoftDist =
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v dist {1 := 1, 2 := 3}; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";
  auto d = ParseWithPreprocessor(In("1800-2012", kSoftDist));
  ASSERT_NE(d.cu, nullptr);
  ASSERT_EQ(d.cu->classes.size(), 1u);
  EXPECT_FALSE(d.has_errors);
  auto here = TallySoft(d, "v");
  EXPECT_EQ(here.dists, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.relations, 0u);

  auto in_2009 = ParseWithPreprocessor(In("1800-2009", kSoftDist));
  EXPECT_TRUE(ReportedError(in_2009.diags, kItemsDoNotParse, LineInRegion(3),
                            "A.1.10"));
  auto there = TallySoft(in_2009, "v");
  EXPECT_EQ(there.dists, 0u)
      << "an ordinary identifier qualifies no distribution";
  EXPECT_EQ(there.refs, 0u);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog1995WordsStillWork) {
  ExpectVerilog1995ConstructsParse("1800-2012");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog2005WordStillWorks) {
  ExpectVerilog2005ConstructsParse("1800-2012");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog2001WordsStillWork) {
  ExpectVerilog2001ConstructsParse("1800-2012");
  ExpectConfigurationWordsParse("1800-2012");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedSystemVerilog2005WordsStillWork) {
  ExpectSystemVerilog2005ConstructsParse("1800-2012");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedSystemVerilog2009WordsStillWork) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "let gain = 21;\n"
      "module m (input logic clk, input logic req, input logic a,\n"
      "          input logic b);\n"
      "  logic [1:0] sel; logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  handshake u_chk (clk, req);\n"
      "  property p; @(posedge clk) s_eventually a until_with b; endproperty\n"
      "  assert property (p);\n"
      "  initial begin\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "    unique0 if (req) r = 8'd3; else r = 8'd4;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "handshake");
  EXPECT_TRUE(
      HasItemKindNamed(r.cu->cu_items, ModuleItemKind::kLetDecl, "gain"));

  auto& items = r.cu->modules[0]->items;
  auto* sum = FindItemByKind(items, ModuleItemKind::kLetDecl);
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->name, "sum");
  ASSERT_EQ(sum->func_args.size(), 2u);
  EXPECT_EQ(sum->func_args[0].data_type.kind, DataTypeKind::kImplicit);
  EXPECT_EQ(sum->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p"));

  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kRestrictProperty), nullptr);
  auto* clocking = FindItemByKind(items, ModuleItemKind::kClockingBlock);
  ASSERT_NE(clocking, nullptr);
  EXPECT_TRUE(clocking->is_global_clocking);

  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  size_t qualified = 0;
  for (auto* st : init->body->stmts) {
    if (st == nullptr) continue;
    if (st->kind != StmtKind::kCase && st->kind != StmtKind::kIf) continue;
    EXPECT_EQ(st->qualifier, CaseQualifier::kUnique0);
    ++qualified;
  }
  EXPECT_EQ(qualified, 2u);

  auto included = ParseWithPreprocessor(In("1800-2005", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2012LeavesWordsOutsideTheTablesAsIdentifiers) {
  const char* const kNotWords[] = {
      "implement", "implements_", "interconnects", "nettypes",
      "net_type",  "softly",      "soft_",
  };
  for (const char* word : kNotWords) {
    auto r = ParseWithPreprocessor(In("1800-2012", VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    auto typed = ParseWithPreprocessor(In("1800-2012", as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace
