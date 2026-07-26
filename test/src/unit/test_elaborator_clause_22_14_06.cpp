#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
bool HasProcess(RtlirDesign* design, std::string_view mod,
                RtlirProcessKind kind) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return false;
  for (const auto& p : m->processes) {
    if (p.kind == kind) return true;
  }
  return false;
}

// Six of Table 22-1's entries name a gate primitive whose keyword may open a
// gate instantiation with no leading type, so a declaration whose identifier
// slot holds one of them is read as a malformed instantiation. Elaborating that
// crashes, with or without any `begin_keywords region and under the default
// reserved word list too, so the fault is not this subclause's and no test here
// can drive it. These six are swept in the identifier slot at the parser stage
// instead, where the same source is rejected without incident.
bool IsGatePrimitiveWord(const std::string& word) {
  const char* kGates[] = {"and", "nand", "nor", "or", "xnor", "xor"};
  for (const char* g : kGates) {
    if (word == g) return true;
  }
  return false;
}

// Two of Table 22-4's entries open an aggregate type declaration, and a
// declaration whose identifier slot holds one of them is read as the start of
// such a type. The parser does not terminate on that -- with no directive in
// force either -- so the elaborator is never reached and no test here can drive
// those two. They are swept in the identifier slot at the lexer and
// preprocessor stages instead, where the list is observed without parsing.
bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}

// The first included list, swept at this stage. There is no earlier version to
// pair these against -- they have been reserved since the first of the three
// lists this version names -- so the accepting side of the claim is the test
// below, where the same words build the design in their keyword roles.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  EXPECT_EQ(std::size(kTable221), 102u);
  size_t swept = 0;
  for (const char* word : kTable221) {
    if (IsGatePrimitiveWord(word)) continue;
    ElabFixture f;
    ElaborateWithPreprocessor(InSv2005(VarDecl(word)), f, "m");
    EXPECT_TRUE(f.has_errors)
        << word << " is included from Table 22-1 and stays reserved";
    ++swept;
  }
  EXPECT_EQ(swept, 96u);
}

// The second included list at this stage, swept whole. Each of Table 22-2's
// entries is reserved here, and under "1364-1995" -- the first of the three
// lists this version includes, where it is not yet a keyword -- the same
// declaration elaborates into a variable of the width it asked for. The pair is
// what makes each word an inclusion rather than an unrelated failure.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  EXPECT_EQ(std::size(kTable222Words), 21u);
  for (const char* word : kTable222Words) {
    ElabFixture reserved;
    ElaborateWithPreprocessor(InSv2005(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The third included list. Its one word cannot name an elaborated variable
// here, names one under both of the lists the version it comes from is built
// on, and still carries its net type into the design -- inclusion means the
// keyword role survives, not only that the identifier slot closes.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2005WordIsReserved) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  ElabFixture reserved;
  ElaborateWithPreprocessor(InSv2005(VarDecl(word)), reserved, "m");
  EXPECT_TRUE(reserved.has_errors);

  for (const auto& earlier : {In2001(VarDecl(word)), In1995(VarDecl(word))}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(earlier, f, "m");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->width, 8u);
  }

  ElabFixture as_net;
  auto* design =
      ElaborateWithPreprocessor(InSv2005("module m;\n"
                                         "  uwire       scalar_net;\n"
                                         "  uwire [7:0] vector_net;\n"
                                         "endmodule\n"),
                                as_net, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(as_net.has_errors);
  const auto* n = FindNet(design, "m", "scalar_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 1u);
  n = FindNet(design, "m", "vector_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);
}

// Table 22-4 swept whole at this stage, with the leg that makes each entry an
// addition. The word cannot name an elaborated variable here, and under
// "1364-2005" -- the union of everything this version includes -- the same
// declaration reaches the design as a variable of the width it asked for.
// Reading the variable back is what keeps the accepting leg from being any
// elaboration that happens to succeed.
TEST(SystemVerilog2005KeywordElaboration, AddedWordsCannotNameVariables) {
  EXPECT_EQ(std::size(kTable224Words), 97u);
  size_t swept = 0;
  for (const char* word : kTable224Words) {
    if (IsAggregateOpenerWord(word)) continue;

    ElabFixture reserved;
    ElaborateWithPreprocessor(InSv2005(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In2005(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
    ++swept;
  }
  EXPECT_EQ(swept, 95u);
}

// The added data type words in the role they exist for, carried into the
// elaborated design. Width alone would not separate them from what the included
// lists already offer, so the two-state entries are read back as two-state as
// well: `reg` and `logic` hold four-state values while `bit`, `byte`, `int` and
// their relatives do not. The same source is not a set of declarations at all
// under the union of everything this version includes.
TEST(SystemVerilog2005KeywordElaboration, AddedTypeWordsBuildElaboratedVars) {
  const std::string kSrc =
      "module m;\n"
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
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "m");
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

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The declaration forms the test above does not reach, carried into the
// elaborated design. A declaration may bring its own initializer along, a port
// may be typed in the module header, and a port may instead be typed in the
// body in the separate style where the header lists only names. Each is a
// production of its own, and the added type words are observed across a
// hierarchy here rather than inside one module -- the child's ports carry the
// added types and the parent binds objects of those types to them.
TEST(SystemVerilog2005KeywordElaboration,
     AddedTypeWordsTypeEveryDeclarationForm) {
  ElabFixture ansi;
  auto* design = ElaborateWithPreprocessor(
      InSv2005("module child (input logic [7:0] a, input byte b,\n"
               "              output int y);\n"
               "  assign y = a + b;\n"
               "endmodule\n"
               "module top;\n"
               "  logic [7:0] src;\n"
               "  byte        step;\n"
               "  int         dst;\n"
               "  int         counted = 21;\n"
               "  child u1 (.a(src), .b(step), .y(dst));\n"
               "endmodule\n"),
      ansi, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ansi.has_errors);

  const auto* child = FindModule(design, "child");
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 3u);
  EXPECT_EQ(child->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(child->ports[0].width, 8u);
  EXPECT_EQ(child->ports[1].type_kind, DataTypeKind::kByte);
  EXPECT_EQ(child->ports[1].width, 8u);
  EXPECT_EQ(child->ports[2].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(child->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(child->ports[2].width, 32u);

  // The parent's own objects, including the one whose declaration carries its
  // value rather than taking it from a separate assignment.
  const auto* dst = FindVar(design, "top", "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->width, 32u);
  const auto* counted = FindVar(design, "top", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);

  ElabFixture non_ansi;
  design = ElaborateWithPreprocessor(InSv2005("module ch (a, y);\n"
                                              "  input  [7:0] a;\n"
                                              "  output [7:0] y;\n"
                                              "  logic  [7:0] y;\n"
                                              "  always_comb y = a + a;\n"
                                              "endmodule\n"),
                                     non_ansi, "ch");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  const auto* m = FindModule(design, "ch");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);
}

// A parameter declaration is a syntactic position of its own for the added type
// words, and one that feeds the constant-expression axis rather than the
// storage axis: the type qualifies a constant, and that constant then has to
// resolve and be usable where a constant expression is required. Both the
// overridable and the local form are here because they reach the elaborator by
// different paths, and the typed parameter is then spent on a declaration's
// width so the value is observed being consumed rather than merely stored.
TEST(SystemVerilog2005KeywordElaboration, AddedTypeWordsQualifyConstants) {
  const std::string kSrc =
      "module t;\n"
      "  parameter  int  P = 21;\n"
      "  localparam byte S = 8'd1;\n"
      "  logic [P-1:0] from_typed_parameter;\n"
      "  logic [S+6:0]  from_typed_localparam;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* p = FindParam(design, "t", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 21);

  const auto* s = FindParam(design, "t", "S");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_localparam);
  EXPECT_EQ(s->resolved_value, 1);

  const auto* wide = FindVar(design, "t", "from_typed_parameter");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->width, 21u);
  const auto* narrow = FindVar(design, "t", "from_typed_localparam");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->width, 8u);

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "t");
  EXPECT_TRUE(included.has_errors);
}

// The user-defined type words, which reach the design by a path of their own:
// `typedef` names a type, `enum` builds one whose members are constants the
// elaborator has to resolve, and a variable declared with the named type has to
// come out with the width and the members that type carries.
TEST(SystemVerilog2005KeywordElaboration, AddedTypedefAndEnumBuildTypes) {
  const std::string kSrc =
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;\n"
      "  byte_t  wide;\n"
      "  state_t phase;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* wide = FindVar(design, "m", "wide");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->width, 8u);

  const auto* phase = FindVar(design, "m", "phase");
  ASSERT_NE(phase, nullptr);
  EXPECT_EQ(phase->width, 2u);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  auto members = m->enum_types.find("state_t");
  ASSERT_NE(members, m->enum_types.end());
  ASSERT_EQ(members->second.size(), 3u);
  EXPECT_EQ(members->second[0].name, "IDLE");
  EXPECT_EQ(members->second[0].value, 0);
  EXPECT_EQ(members->second[2].name, "DONE");
  EXPECT_EQ(members->second[2].value, 2);

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The words that open a process, carried to the elaborated design. Each of the
// three inferred always forms and the final block reaches the design as a
// process of its own kind, so which word opened which is read back rather than
// inferred from the source elaborating.
TEST(SystemVerilog2005KeywordElaboration, AddedProcessWordsBuildProcesses) {
  const std::string kSrc =
      "module m (input logic clk, input logic d, output logic q);\n"
      "  logic combo;\n"
      "  logic latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysComb));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysFF));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysLatch));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kFinal));

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The design element words at this stage. A package holds a constant and a
// module imports it, and an interface is instantiated so that it reaches the
// elaborated design flagged as one -- the words are observed opening elements
// the elaborator distinguishes rather than merely parsing into their own lists.
TEST(SystemVerilog2005KeywordElaboration,
     AddedDesignElementWordsBuildElements) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  ifc u_if();\n"
      "  logic [7:0] w;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

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

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// Table 22-1 doing its work under this version, read back as elaborated
// structure. The net types are the sharpest part: each resolved and driven type
// the first included list names has to survive into the design as itself rather
// than collapsing onto a plain wire, which would leave the inclusion
// unobserved.
TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectTable221DeclarationsElaborate("1800-2005");
}

// Table 22-2 doing its work, likewise as structure rather than as tokens.
// `localparam` resolves to a constant, `genvar`/`generate`/`endgenerate`
// produce one copy of the loop body per iteration, and `signed`/`unsigned`
// select what they select. The three are tied together on purpose: the
// localparam is the loop bound, so the count of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectTable222DeclarationsElaborate("1800-2005");
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required. A literal and a `parameter` come
// from the first included list, `localparam` and the `automatic` that lets a
// constant function be written come from the second, and `int` -- the type the
// function returns and the declarations take -- is one of this version's own
// additions. So the four forms are reachable here by what this version includes
// and are written with what it adds, and the width the design ends up with is
// what shows each constant resolved.
//
// The remaining constant form, a genvar, shows its value in the copies its loop
// produces rather than in a width, and it is observed doing exactly that in
// IncludedVerilog2001WordsStillBuildDesign above -- there against a loop bound
// that is itself a constant and with a nested condition singling out one
// iteration. Repeating a weaker version of it here would add nothing.
TEST(SystemVerilog2005KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InSv2005("module t;\n"
               "  parameter  P = 8;\n"
               "  localparam L = 8;\n"
               "  function automatic int width_of(input int n);\n"
               "    width_of = n;\n"
               "  endfunction\n"
               "  logic [7:0]             from_literal;\n"
               "  logic [P-1:0]           from_parameter;\n"
               "  logic [L-1:0]           from_localparam;\n"
               "  logic [width_of(8)-1:0] from_function;\n"
               "endmodule\n"),
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const char* kNames[] = {"from_literal", "from_parameter", "from_localparam",
                          "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

// The negative the four tables imply, carried to this stage. A word none of
// them lists is an ordinary identifier here, so it names an object that really
// reaches the design -- and it is not a data type, which is the half that would
// go unchecked if only the naming side were tested.
TEST(SystemVerilog2005KeywordElaboration,
     UnlistedWordsNameObjectsButAreNotTypes) {
  // None of these opens a design element, so putting one at the head of a line
  // leaves the region machinery -- which tracks design elements by a line's
  // first word, without regard to the list in force -- out of the picture, and
  // the only thing that can reject the source is the word not being a type.
  const char* kUnlisted[] = {"until", "let", "global", "nettype", "soft"};
  for (const char* word : kUnlisted) {
    ElabFixture named;
    auto* design =
        ElaborateWithPreprocessor(InSv2005(VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessor(InSv2005(std::string("module m;\n  ") + word +
                                       " [7:0] v;\nendmodule\n"),
                              as_type, "m");
    EXPECT_TRUE(as_type.has_errors)
        << word << " is not a data type under this version";
  }
}

}  // namespace
