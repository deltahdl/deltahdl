#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The five included lists swept whole in an identifier slot, table by table.
// Each entry is reserved under this version, and -- for every list but the
// first, which has no earlier version to be measured against -- the same
// declaration elaborates into a variable of the width it asked for under the
// union of the lists that one is built on. The five sweeps share one test
// because they share one shape; the table name travels with every failure
// message. What they do not show is the keyword roles surviving, which the
// tests further down carry, one per included list.
TEST(SystemVerilog2012KeywordElaboration, IncludedWordsAreReservedAtThisStage) {
  for (const auto& table : {kSweepTable221, kSweepTable222, kSweepTable223,
                            kSweepTable224, kSweepTable225}) {
    ExpectKeywordTableIsReserved("1800-2012", table);
  }

  ExpectConfigurationWordsNameVariablesUnderNoconfig();
}

// Table 22-6 swept at this stage, with the leg that makes each entry an
// addition. The word cannot name an elaborated variable here, and under
// "1800-2009" -- the union of everything this version includes -- the same
// declaration reaches the design as a variable of the width it asked for.
// Reading it back keeps the accepting leg from being any elaboration that
// happens to succeed.
TEST(SystemVerilog2012KeywordElaboration, AddedWordsCannotNameVariables) {
  ExpectKeywordTableIsReserved("1800-2012", kSweepTable226);
}

// The added word whose construct becomes elaborated structure of its own kind.
// An interconnect net carries a net type no other word produces -- scalar and
// vector, in a port as well as in a declaration -- while the ordinary net
// beside it does not. Two elaborator rules turn on that mark: the generic
// connection carries no signedness, and it is not a net a declaration may drive
// from its own initializer. Each is shown against the ordinary net allowed
// exactly what it is refused.
TEST(SystemVerilog2012KeywordElaboration, AddedInterconnectNetsReachTheDesign) {
  const std::string kSrc =
      "module m (interconnect [3:0] p, inout interconnect [7:0] q,\n"
      "          input interconnect [1:0] r, output interconnect s,\n"
      "          input wire a, output wire y);\n"
      "  interconnect       scalar_ic;\n"
      "  interconnect [7:0] bus_ic;\n"
      "  wire         [7:0] plain;\n"
      "  assign y = a;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "scalar_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 1u);
  n = FindNet(design, "m", "bus_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->net_type, NetType::kInterconnect);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  // The mark survives every direction a port header may name, and the width
  // still comes from the packed range written beside the word. A generic
  // connection with no direction named is bidirectional, which is what the
  // first row records.
  ASSERT_EQ(m->ports.size(), 6u);
  struct PortCase {
    size_t index;
    Direction direction;
    uint32_t width;
  };
  const PortCase kMarked[] = {{0, Direction::kInout, 4},
                              {1, Direction::kInout, 8},
                              {2, Direction::kInput, 2},
                              {3, Direction::kOutput, 1}};
  for (const auto& c : kMarked) {
    EXPECT_TRUE(m->ports[c.index].is_interconnect) << c.index;
    EXPECT_EQ(m->ports[c.index].direction, c.direction) << c.index;
    EXPECT_EQ(m->ports[c.index].width, c.width) << c.index;
  }
  EXPECT_FALSE(m->ports[4].is_interconnect);

  // The first rule keyed off the mark: the generic connection has no
  // signedness, while an ordinary port may be declared signed.
  ElabFixture signed_ic;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (interconnect signed [3:0] p);\nendmodule\n"),
      signed_ic, "m");
  EXPECT_TRUE(signed_ic.has_errors);
  ElabFixture signed_wire;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (input wire signed [3:0] p);\nendmodule\n"),
      signed_wire, "m");
  EXPECT_FALSE(signed_wire.has_errors);

  // The second: an interconnect net takes no declaration assignment, while an
  // ordinary net does.
  ElabFixture ic_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  interconnect [3:0] q = 4'd1;\nendmodule\n"),
      ic_assign, "m");
  EXPECT_TRUE(ic_assign.has_errors);
  ElabFixture wire_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  wire [3:0] q = 4'd1;\nendmodule\n"),
      wire_assign, "m");
  EXPECT_FALSE(wire_assign.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word that binds a name to a net's data type. What the elaborator
// settles is the width every net declared with that name gets, so the nets are
// read back rather than the declaration. Both forms of the declaration are here
// and so is its own elaborator rule -- not every data type may stand in it --
// which is a diagnostic only a keyword can raise.
TEST(SystemVerilog2012KeywordElaboration,
     AddedNettypeDeclarationsResolveNetWidths) {
  const std::string kSrc =
      "module m;\n"
      "  function automatic real resolve_sum(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype byte_net    alias_net;\n"
      "  nettype real        analog_net with resolve_sum;\n"
      "  byte_net  wide;\n"
      "  alias_net through;\n"
      "  analog_net resolved;\n"
      "  wire      plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "wide");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "through");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u) << "the second name resolves through the first";
  // The second form of the declaration, which also names the function resolving
  // multiple drivers; the width still comes from the type the name was bound
  // to.
  n = FindNet(design, "m", "resolved");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 64u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 1u);

  // A nettype whose data type is not one a net may carry.
  ElabFixture bad_type;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  nettype string text_net;\nendmodule\n"),
      bad_type, "m");
  EXPECT_TRUE(bad_type.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word whose clause the elaborator itself acts on. Naming an
// interface class puts the implementing class under an obligation the
// elaborator checks: a class supplying every prototype elaborates clean, and
// the same class with one method removed is rejected. Both are shown, since the
// accepting leg alone would be consistent with the clause being ignored.
TEST(SystemVerilog2012KeywordElaboration,
     AddedImplementsClauseCarriesObligations) {
  const std::string kSrc =
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class port_t implements reader, writer;\n"
      "  int held;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  // The obligation from the first interface, unmet.
  ElabFixture missing_read;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t implements reader;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            missing_read, "m");
  EXPECT_TRUE(missing_read.has_errors);

  // The same class without the clause is not under the obligation at all, so
  // what the rejection above tracks is the clause rather than the missing
  // method.
  ElabFixture no_clause;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            no_clause, "m");
  EXPECT_FALSE(no_clause.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word with two keyword roles, both reaching this stage. As a union
// qualifier it selects a type whose members share storage, shown in the width
// the variable ends up with: one member's worth rather than the sum. As a
// constraint qualifier it marks a relation the solver may drop, and the
// elaborator applies the rule that such a relation may only be placed on a
// variable randomized without a cycle -- with nothing to attach to when the
// word is an ordinary identifier, as the "1800-2009" leg shows.
TEST(SystemVerilog2012KeywordElaboration, AddedSoftQualifierReachesTheDesign) {
  const std::string kUnion =
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  overlay_t u;\n"
      "  logic [7:0] plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kUnion), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* u = FindVar(design, "m", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u) << "the members share their storage";

  ElabFixture union_included;
  ElaborateWithPreprocessor(In("1800-2009", kUnion), union_included, "m");
  EXPECT_TRUE(union_included.has_errors);

  // The constraint role, and the rule the elaborator applies to it.
  const std::string kCyclic =
      "class c;\n"
      "  randc bit [3:0] v;\n"
      "  constraint cc { soft v == 4'd3; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";
  ElabFixture cyclic;
  ElaborateWithPreprocessor(In("1800-2012", kCyclic), cyclic, "m");
  EXPECT_TRUE(cyclic.has_errors);

  // The same relation on an ordinary random variable is accepted, so the
  // rejection above is the rule and not the qualifier being unusable.
  ElabFixture plain_rand;
  ElaborateWithPreprocessor(In("1800-2012",
                               "class c;\n"
                               "  rand bit [3:0] v;\n"
                               "  constraint cc { soft v == 4'd3; }\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            plain_rand, "m");
  EXPECT_FALSE(plain_rand.has_errors);

  // Under everything this version includes the word qualifies nothing, so the
  // rule never attaches and the very same source elaborates clean.
  ElabFixture constraint_included;
  ElaborateWithPreprocessor(In("1800-2009", kCyclic), constraint_included, "m");
  EXPECT_FALSE(constraint_included.has_errors);
}

// Table 22-1 doing its work, read back as elaborated structure. The net types
// are the sharpest part: each resolved and driven type has to survive into the
// design as itself rather than collapsing onto a plain wire.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectTable221DeclarationsElaborate("1800-2012");
}

// Table 22-3, whose lone entry is a net type of its own and so is read back the
// same way.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog2005WordStillBuildsDesign) {
  ExpectTable223DeclarationsElaborate("1800-2012");
}

// Table 22-2 doing its work, likewise as structure rather than as tokens. The
// constructs are tied together on purpose: the localparam is the loop bound, so
// the count of declarations depends on it resolving, and the nested condition
// picks one iteration, so the genvar holds a different constant each pass.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectTable222DeclarationsElaborate("1800-2012");
}

// The fourth included list doing its work, the largest thing this version
// inherits: data types with their widths and four-state flag, user-defined
// types with their resolved members, inferred processes each as its own kind,
// and the design element words.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2005WordsStillBuildDesign) {
  ExpectTable224DeclarationsElaborate("1800-2012");
}

// The declaration forms the identifier sweeps do not reach, all written with
// types from that same fourth list since the added words bring no ordinary
// data type of their own: a declaration carrying its own initializer, a port
// typed in the module header, and a port typed in the body in the separate
// style where the header lists only names.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedTypeWordsFillTheDeclarationFormsSweepsMiss) {
  const std::string kSrc =
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  logic  [7:0] y;\n"
      "  always_comb y = a + a;\n"
      "endmodule\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  int  counted = 21;\n"
      "  logic [7:0] as_logic;\n"
      "  wire  [7:0] ch_out;\n"
      "  ch u_ch (as_logic, ch_out);\n"
      "  always_comb q = d & clk;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* counted = FindVar(design, "m", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 3u);
  EXPECT_EQ(m->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(m->ports[2].direction, Direction::kOutput);

  const auto* ch = FindModule(design, "ch");
  ASSERT_NE(ch, nullptr);
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  EXPECT_EQ(ch->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);
}

// The fifth included list doing its work: the `let` declaration lands in lists
// of its own at both scopes, the checker element resolves through an
// instantiation, the marked clocking block is counted by a rule that rejects a
// second one, and the permissive case qualifier survives into the process.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2009WordsStillBuildDesign) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "let gain = 21;\n"
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  handshake u_chk (clk, req);\n"
      "  initial begin\n"
      "    sel = 2'b01;\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "  end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ExpectLetDeclarationsElaborated(design);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);

  bool instance_seen = false;
  for (const auto& child : m->children) {
    if (child.inst_name == "u_chk") {
      EXPECT_EQ(child.module_name, "handshake");
      instance_seen = true;
    }
  }
  EXPECT_TRUE(instance_seen);

  bool qualified_case_seen = false;
  for (const auto& proc : m->processes) {
    if (proc.kind != RtlirProcessKind::kInitial || proc.body == nullptr)
      continue;
    for (auto* s : proc.body->stmts) {
      if (s != nullptr && s->kind == StmtKind::kCase) {
        EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
        qualified_case_seen = true;
      }
    }
  }
  EXPECT_TRUE(qualified_case_seen);

  // The rule that counts the mark on a clocking block: a second marked block in
  // the same scope is rejected.
  ElabFixture two_global;
  ElaborateWithPreprocessor(
      In("1800-2012",
         "module m (input logic clk);\n"
         "  global clocking gcb  @(posedge clk); endclocking\n"
         "  global clocking gcb2 @(negedge clk); endclocking\n"
         "endmodule\n"),
      two_global, "m");
  EXPECT_TRUE(two_global.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2005", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required. A literal and a `parameter` come
// from the first included list, `localparam` and the `automatic` that lets a
// constant function be written from the second, and `int` from the fourth. The
// fifth form, a genvar, shows its value in the copies its loop produces and is
// observed doing that in IncludedVerilog2001WordsStillBuildDesign above.
TEST(SystemVerilog2012KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ExpectEveryConstantFormResolves("1800-2012", "int ", "byte");
}

// The negative the six tables imply, carried to this stage. A word none of them
// lists is an ordinary identifier here, so it names an object that reaches the
// design -- and it is not a data type, the half that would go unchecked if only
// the naming side were tested. Each word is a near miss of a real entry, since
// this version is the last that reserves anything new.
TEST(SystemVerilog2012KeywordElaboration,
     WordsOutsideTheTablesNameObjectsButAreNotTypes) {
  ExpectWordsNameObjectsButAreNotTypes(
      "1800-2012", {"implement", "implements_", "interconnects", "nettypes",
                    "net_type", "softly", "soft_"});
}

}  // namespace
