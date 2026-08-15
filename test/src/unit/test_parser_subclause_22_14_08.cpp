#include <cstddef>
#include <iterator>
#include <map>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_identifier_positions.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// What a constraint block recorded for the fourth added word. Shared by the two
// tests below so each reads as a tally rather than as a walk.
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

// The five included lists swept whole in an identifier slot, table by table.
// Each entry is rejected under this version, and -- for every list but the
// first, which has no earlier version to be measured against -- the very same
// declaration is accepted under the union of the lists that one is built on and
// read back off the tree, so the rejection is this version's list doing its
// work rather than an unrelated parse failure. The table name travels with
// every failure message. What the sweeps do not show is the keyword roles
// surviving, which the tests further down carry, one per included list.
TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryIncludedKeyword) {
  for (const auto& table : {kSweepTable221AtParse, kSweepTable222,
                            kSweepTable223, kSweepTable224, kSweepTable225}) {
    ExpectKeywordTableIsReservedAtParse("1800-2012", table);
  }

  ExpectConfigurationWordsNameVariablesAtParse();
}

// Table 22-6 swept in an identifier slot, with the leg that makes each entry an
// addition. The word cannot name a variable here, and under "1800-2009" -- the
// union of everything this version includes -- the very same declaration is
// built and read back off the tree. Both legs together make the word this
// version_specifier's own rather than anything it inherits.
TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2012", kSweepTable226);
}

// Being on this version's list has to stop a word from naming anything at all,
// so one word from each of the five *included* tables is put in turn in every
// position above. Table 22-6 is absent here on purpose: its position axis is
// carried by the test below, which runs the same table against all four added
// words and asserts this rejection alongside its accepting counterpart.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2012", {"wire", "generate", "uwire", "logic", "until"});
}

// The other side of the addition across those same positions. The sweep above
// closes the variable-declaration slot but does not show the added words free
// in any *other* position under the lists this version includes. So all four
// are put in every position under "1800-2009", where they are still ordinary
// identifiers, each paired with the same source under this version. None of
// the four opens a design element, so the region machinery stays out of the
// way.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder(
      "1800-2009", "1800-2012",
      {"implements", "interconnect", "nettype", "soft"});

  // Two of those positions read back, so the accepting legs are observed naming
  // things rather than merely parsing.
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

// The first of the keyword roles this version's additions exist for: the clause
// by which a class declares the interface classes it honours. Two named in one
// clause land as two entries, kept apart from the single base inherited through
// the older `extends` of the fourth included list, whose `interface` and `pure
// virtual` the interface classes are themselves written with.
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
  // The clause this version adds is distinct from the inheritance clause the
  // fourth included list already offers.
  EXPECT_EQ(impl->base_class, "base");

  // §8.3 owns the report: with `implements` an ordinary identifier the
  // extends clause on line 10 ends where it stands, and Parser::ParseClassDecl
  // is looking for the semicolon that closes the class header.
  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ';', got identifier",
                            LineInRegion(10), "8.3"));
}

// The second added word, which opens a net whose type is left to be settled by
// what it connects. It is written in the two positions the production admits --
// a declaration inside a design element and a port in the header -- each
// landing with the mark that separates it from an ordinary net. The optional
// signedness and packed dimensions are exercised too, being parsed by the same
// branch.
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

  // §23.2.2.1 owns the report: with `interconnect` an ordinary identifier and
  // no direction ahead of it, the header reads as a non-ANSI port list whose
  // first entry is the name `interconnect` with a part select, which leaves
  // `p` where Parser::ParseNonAnsiPortList wants the closing parenthesis.
  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ')', got identifier",
                            LineInRegion(1), "23.2.2.1"));
}

// The direction and signedness qualifiers the interconnect form admits, which
// the test above does not reach: the word may stand behind each of the three
// directions a port header names, and the declaration takes the unsigned
// qualifier as well as the signed one. Every form is refused under the union of
// the lists this version includes.
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
  // §23.2.2.2 owns the report: the direction makes the header ANSI, so
  // `interconnect` is read as the first port's own name and `[3:0]` as its
  // unpacked dimension, leaving `a` where Parser::ParsePortList wants the
  // closing parenthesis.
  auto included = ParseWithPreprocessor(In("1800-2009", kPorts));
  EXPECT_TRUE(ReportedError(included.diags, "expected ')', got identifier",
                            LineInRegion(1), "23.2.2.2"));

  // The declaration form's other signedness qualifier.
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
  // §6.8 owns the report: with `interconnect` an ordinary identifier,
  // Parser::ParsePlainVarDecl reads it as a variable of an implicit type and
  // demands the semicolon where `unsigned` stands.
  auto included_unsigned = ParseWithPreprocessor(In("1800-2009", kUnsigned));
  EXPECT_TRUE(ReportedError(included_unsigned.diags,
                            "expected ';', got 'unsigned'", LineInRegion(2),
                            "6.8"));
}

// The third added word, which opens a declaration binding a name to a net's
// data type. Both forms are here: the plain one and the one naming the function
// that resolves multiple drivers, each read back with the type it bound. The
// production's own negative -- the data type is not optional -- is here too,
// and it is a diagnostic only a keyword can raise.
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

  // The declaration's own negative: the data type is required, which
  // Parser::ParseNettypeDecl states under §6.6.7 at the keyword itself.
  auto typeless = ParseWithPreprocessor(
      In("1800-2012", "module m;\n  nettype lone;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(typeless.diags,
                            "nettype declaration requires an explicit data "
                            "type",
                            LineInRegion(2), "6.6.7"));

  // §6.8 owns the report under the included lists: with `nettype` an ordinary
  // identifier, Parser::ParsePlainVarDecl reads it as a variable of an
  // implicit type and demands the semicolon where `logic` stands.
  auto included = ParseWithPreprocessor(In("1800-2009", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected ';', got 'logic'",
                            LineInRegion(5), "6.8"));
}

// The remaining forms of the declaration the third added word opens: the
// resolution function may be reached through a package scope rather than by a
// bare name, a branch of its own, and the declaration is a package item as well
// as a design-element item. Neither can be written under the included lists.
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
  // The trailing name is the resolver; the scope qualifying it is consumed by
  // the same branch.
  EXPECT_EQ(scoped->nettype_resolve_func, "res");
  // §6.8 owns the report, as it does for the plain form: `nettype` reads as a
  // variable of an implicit type and Parser::ParsePlainVarDecl demands the
  // semicolon where `real` stands.
  auto included_scoped = ParseWithPreprocessor(In("1800-2009", kScoped));
  EXPECT_TRUE(ReportedError(included_scoped.diags, "expected ';', got 'real'",
                            LineInRegion(7), "6.8"));

  // The second position: a package item rather than a design-element item.
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

// The fourth added word, the only one with two unrelated keyword roles, so both
// are here. As a union qualifier it marks a type whose members overlay one
// another without being packed; in a constraint block it marks a relation the
// solver may drop and discards the relations already placed on a variable. Its
// negative is the qualifier's own exclusivity rule: a union takes at most one
// of the two qualifiers it admits.
//
// The constraint half has no paired rejection under "1800-2009": a constraint
// body is scanned token by token rather than parsed as a grammar, so a stray
// identifier where the word stood is absorbed. What the pairing shows there is
// that nothing is *captured*. The union half does reject outright.
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
  // §7.2 owns the report: with `soft` an ordinary identifier it stands where
  // Parser::ParseStructOrUnionType admits nothing between `union` and its
  // member list.
  auto included_union = ParseWithPreprocessor(In("1800-2009", kUnion));
  EXPECT_TRUE(ReportedError(included_union.diags,
                            "union declarations may not have a tag before '{'",
                            LineInRegion(2), "7.2"));

  // The qualifier's exclusivity rule, which only attaches when the word is read
  // as a qualifier at all. §7.2 states it, and Parser::ParseUnionQualifiers
  // reports it at the second qualifier.
  auto both = ParseWithPreprocessor(
      In("1800-2012",
         "module m;\n"
         "  typedef union soft tagged { logic [7:0] a; } both_t;\n"
         "endmodule\n"));
  EXPECT_TRUE(ReportedError(both.diags,
                            "union may have at most one of 'soft' or 'tagged'",
                            LineInRegion(2), "7.2"));

  // Both constraint productions the word appears in: the qualifier that opens a
  // droppable relation, and the directive that discards the relations already
  // placed on a variable. They are written in separate blocks so each is
  // counted on its own.
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
  // One qualified relation captured; the two hard ones beside it are not.
  EXPECT_EQ(here.relations, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.discarded, 1u);

  auto included = ParseWithPreprocessor(In("1800-2009", kConstraint));
  ASSERT_NE(included.cu, nullptr);
  ASSERT_EQ(included.cu->classes.size(), 1u);
  auto there = TallySoft(included, "v");
  EXPECT_EQ(there.blocks, 2u);
  EXPECT_EQ(there.relations, 0u) << "an ordinary identifier qualifies nothing";
  EXPECT_EQ(there.refs, 0u);
  EXPECT_EQ(there.discarded, 0u) << "and discards nothing";
}

// The remaining positions the fourth added word may qualify: a union type
// written straight into a data declaration rather than through a typedef, and a
// distribution rather than a plain relation inside a constraint block, recorded
// on a list of its own. The declaration form is refused outright under the
// included lists; the constraint form instead records nothing there.
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
  // §7.2 owns the report here too: with `soft` an ordinary identifier it
  // stands where Parser::ParseStructOrUnionType admits nothing between `union`
  // and its member list.
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
  // The distribution is captured on a list of its own, not as a plain relation.
  EXPECT_EQ(here.dists, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.relations, 0u);

  auto there =
      TallySoft(ParseWithPreprocessor(In("1800-2009", kSoftDist)), "v");
  EXPECT_EQ(there.dists, 0u)
      << "an ordinary identifier qualifies no distribution";
  EXPECT_EQ(there.refs, 0u);
}

// Table 22-1 in its keyword role: inclusion is not only about what a word may
// no longer name. The gate primitives build structure, the resolved net types
// and drive strengths are written out, and the procedural statements build
// control flow.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog1995WordsStillWork) {
  ExpectTable221ConstructsParse("1800-2012");
}

// Table 22-3, whose lone entry opens a net declaration and types a port.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog2005WordStillWorks) {
  ExpectTable223ConstructsParse("1800-2012");
}

// Table 22-2 in its keyword role: a constant declaration, a loop generate
// construct, a subroutine qualifier, the signedness qualifiers, and the four
// pulse-control specify items. Its other half is the ten words a configuration
// is written with, which separates this list from its configuration-free
// companion: seven appear below and the declaration is built, while under that
// companion the very same source cannot be written.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog2001WordsStillWork) {
  ExpectTable222ConstructsParse("1800-2012");
  ExpectConfigurationWordsParse("1800-2012");
}

// The fourth included list in its keyword role, the largest thing this version
// inherits: data types, user-defined types, inferred processes, design
// elements, and the verification vocabulary the added words sit alongside.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedSystemVerilog2005WordsStillWork) {
  ExpectTable224ConstructsParse("1800-2012");
}

// The fifth included list in its keyword role: a design element of its own, a
// declaration, an untyped formal, a case qualifier that permits no match, a
// restriction item, the single clocking block a design may mark, and the
// temporal operators a property expression is built from. None of it can be
// written under "1800-2005", the union of the lists that one is built on.
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

  // §3.12.1 owns the report: with `checker` an ordinary identifier the first
  // line heads nothing the compilation unit admits, and Parser::ParseTopLevel
  // says so at src/parser/parser.cpp:499.
  auto included = ParseWithPreprocessor(In("1800-2005", kSrc));
  EXPECT_TRUE(ReportedError(included.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

// The negative the six tables imply: a word none of them lists is an ordinary
// identifier under this version, so it names things freely and opens nothing.
// Both halves are here -- the same word naming a declaration and failing to be
// a data type -- because either alone would leave the other unchecked. This
// version is the last that reserves anything new, so what is bounded is the
// table's own membership: each word is a near miss of a real entry.
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
    // §6.8 owns the report: the word is an ordinary identifier here, so
    // Parser::ParsePlainVarDecl reads it as a variable of an implicit type and
    // the packed dimension is where it expected the declaration to end.
    auto typed = ParseWithPreprocessor(In("1800-2012", as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace
