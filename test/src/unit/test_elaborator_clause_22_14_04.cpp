#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The ten identifiers this version_specifier drops from the list "1364-2001"
// reserves.
constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// The rest of Table 22-2, which this version keeps reserved.
constexpr const char* kKept[] = {
    "automatic",
    "endgenerate",
    "generate",
    "genvar",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
};

// Wraps `body` in a real `begin_keywords region for this version, so the
// reserved word list in force while the design is built is the one the
// directive selected.
std::string InNoconfig(const std::string& body) {
  return "`begin_keywords \"1364-2001-noconfig\"\n" + body + "`end_keywords\n";
}

// The version this one is defined in terms of, and the version it extends.
std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

const RtlirModule* FindModule(RtlirDesign* design, std::string_view name) {
  auto it = design->all_modules.find(name);
  return it == design->all_modules.end() ? nullptr : it->second;
}

const RtlirVariable* FindVar(RtlirDesign* design, std::string_view mod,
                             std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& var : m->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

const RtlirNet* FindNet(RtlirDesign* design, std::string_view mod,
                        std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& net : m->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

const RtlirParamDecl* FindParam(RtlirDesign* design, std::string_view mod,
                                std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& p : m->params) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

// How many elaborated variables in `mod` have a name ending in `suffix`, used
// to observe a loop generate construct without depending on how the elaborator
// spells a per-iteration name.
size_t CountVarsEndingIn(RtlirDesign* design, std::string_view mod,
                         std::string_view suffix) {
  size_t n = 0;
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return n;
  for (const auto& var : m->variables) {
    if (var.name.size() >= suffix.size() &&
        var.name.substr(var.name.size() - suffix.size()) == suffix) {
      ++n;
    }
  }
  return n;
}

// The exception carried to this stage. Being dropped from the reserved list
// has to mean more than lexing as an identifier: each of the ten must name a
// variable that really exists in the elaborated design, carrying the storage
// its declaration asked for. The "1364-2001" leg is what makes each one an
// exception rather than a word that was never reserved.
TEST(NoconfigKeywordElaboration, ExcludedWordsNameElaboratedVariables) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  for (const char* word : kExcluded) {
    std::string decl =
        std::string("module t;\n  reg [7:0] ") + word + ";\nendmodule\n";

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(InNoconfig(decl), freed, "t");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "t", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture reserved;
    ElaborateWithPreprocessor(In2001(decl), reserved, "t");
    EXPECT_TRUE(reserved.has_errors) << word;
  }
}

// The complement: the eleven entries of Table 22-2 this subclause does not
// name stay reserved, so none of them reaches the design as a variable. The
// 1364-1995 leg shows the same declaration building one under the list
// "1364-2001" extends, so the rejection is the reserved word list's doing.
TEST(NoconfigKeywordElaboration, KeptAdditionsCannotNameElaboratedVariables) {
  EXPECT_EQ(std::size(kKept), 11u);
  for (const char* word : kKept) {
    std::string decl =
        std::string("module t;\n  reg [7:0] ") + word + ";\nendmodule\n";

    ElabFixture reserved;
    ElaborateWithPreprocessor(InNoconfig(decl), reserved, "t");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(decl), freed, "t");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "t", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The elaborated design keeps nets and constants in containers of their own,
// separate from the variables above, so a dropped word has to survive each of
// those paths in its own right. This also puts both sides of the rule in one
// declaration list: the constants are introduced by `parameter`, inherited
// from Table 22-1, and by `localparam`, an addition this version keeps, while
// every name they carry is one of the ten it drops.
TEST(NoconfigKeywordElaboration, ExcludedWordsNameElaboratedNetsAndConstants) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(InNoconfig("module m;\n"
                                           "  wire [7:0] library;\n"
                                           "  wand       liblist;\n"
                                           "  parameter  incdir = 8;\n"
                                           "  localparam include = 9;\n"
                                           "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "library");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  EXPECT_EQ(n->net_type, NetType::kWire);

  n = FindNet(design, "m", "liblist");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWand);

  const auto* p = FindParam(design, "m", "incdir");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);

  p = FindParam(design, "m", "include");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 9);
}

// The declaration kinds the sweep does not reach -- an integer, a real, a time,
// and an event -- each a different path from the declaration into the design.
TEST(NoconfigKeywordElaboration, ExcludedWordsNameEveryVariableKind) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(InNoconfig("module m;\n"
                                           "  reg [63:0] cell;\n"
                                           "  integer    config;\n"
                                           "  real       design;\n"
                                           "  time       endconfig;\n"
                                           "  event      use;\n"
                                           "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* v = FindVar(design, "m", "cell");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "config");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);

  v = FindVar(design, "m", "design");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);

  v = FindVar(design, "m", "endconfig");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "use");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// A dropped word naming the design element itself, its ports, and the instance
// that binds to it: the region governs a whole elaborated hierarchy, not one
// declaration inside one module.
TEST(NoconfigKeywordElaboration, ExcludedWordNamesModulePortsAndInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InNoconfig("module cell (input wire design,\n"
                 "             output wire library);\n"
                 "  assign library = design;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  wire a, b;\n"
                 "  cell config (.design(a), .library(b));\n"
                 "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* child = FindModule(design, "cell");
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 2u);
  EXPECT_EQ(child->ports[0].name, "design");
  EXPECT_EQ(child->ports[0].direction, Direction::kInput);
  EXPECT_EQ(child->ports[1].name, "library");
  EXPECT_EQ(child->ports[1].direction, Direction::kOutput);

  const auto* top = FindModule(design, "top");
  ASSERT_NE(top, nullptr);
  bool found_instance = false;
  for (const auto& inst : top->children) {
    if (inst.inst_name == "config" && inst.module_name == "cell") {
      found_instance = true;
    }
  }
  EXPECT_TRUE(found_instance);
}

// Behaving as "1364-2001" does, observed as elaborated structure rather than
// as tokens: the additions this version keeps still do their job. `localparam`
// resolves to a constant and `genvar`/`generate`/`endgenerate` produce one copy
// of the loop body per iteration. The three are tied together deliberately --
// the localparam is the loop bound, so the number of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
TEST(NoconfigKeywordElaboration, KeptAdditionsStillBuildTheDesign) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InNoconfig("module t;\n"
                 "  localparam L = 4;\n"
                 "  genvar g;\n"
                 "  generate\n"
                 "    for (g = 0; g < L; g = g + 1) begin : blk\n"
                 "      reg [7:0] slot;\n"
                 "      if (g == 1) begin : only_one\n"
                 "        reg [7:0] picked;\n"
                 "      end\n"
                 "    end\n"
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
}

// The other kept additions selecting what they select, which survives into the
// design: the same declared width, differing only in the signedness the
// keyword asked for.
TEST(NoconfigKeywordElaboration, KeptSignedAndUnsignedSelectSignedness) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(InNoconfig("module t;\n"
                                           "  reg signed   [7:0] s;\n"
                                           "  reg unsigned [7:0] u;\n"
                                           "  wire signed  [7:0] n;\n"
                                           "endmodule\n"),
                                f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->width, 8u);
  EXPECT_TRUE(s->is_signed);

  const auto* u = FindVar(design, "t", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u);
  EXPECT_FALSE(u->is_signed);

  const auto* n = FindNet(design, "t", "n");
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_signed);
}

// A dropped word sizing a declaration rather than naming one: each constant
// form this version admits reaches the elaborator by a different path, and all
// three arrive at the same width. Every constant here is carried by one of the
// ten, so the exception is what makes the widths resolvable at all.
TEST(NoconfigKeywordElaboration, ExcludedWordsCarryConstantsThatSizeADecl) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InNoconfig("module t;\n"
                 "  parameter  incdir  = 8;\n"
                 "  localparam liblist = 8;\n"
                 "  function automatic integer use(input reg [7:0] n);\n"
                 "    use = n;\n"
                 "  endfunction\n"
                 "  reg [7:0]           from_literal;\n"
                 "  reg [incdir-1:0]    from_parameter;\n"
                 "  reg [liblist-1:0]   from_localparam;\n"
                 "  reg [use(8)-1:0]    from_function;\n"
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

// The constant form the width test above cannot reach: a genvar. This puts
// both halves of the rule inside one declaration -- `genvar` is one of the
// eleven additions this version keeps, so it still opens the declaration, while
// the name it introduces is one of the ten this version drops. Only a loop
// generate construct shows a genvar doing its job, so the count of the
// per-iteration copies proves it resolved, and the nested condition picking
// one pass proves it held a different constant each time rather than merely
// making the loop run. The loop bound is carried by a second dropped word, so
// the whole construct is driven by names this version freed.
TEST(NoconfigKeywordElaboration, ExcludedWordNamesAGenvarDrivingAGenerateLoop) {
  ElabFixture f;
  auto* built = ElaborateWithPreprocessor(
      InNoconfig("module t;\n"
                 "  localparam incdir = 4;\n"
                 "  genvar design;\n"
                 "  generate\n"
                 "    for (design = 0; design < incdir; design = design + 1)\n"
                 "      begin : blk\n"
                 "        reg [7:0] slot;\n"
                 "        if (design == 1) begin : only_one\n"
                 "          reg [7:0] picked;\n"
                 "        end\n"
                 "      end\n"
                 "  endgenerate\n"
                 "endmodule\n"),
      f, "t");
  ASSERT_NE(built, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* bound = FindParam(built, "t", "incdir");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_localparam);
  EXPECT_EQ(bound->resolved_value, 4);

  EXPECT_EQ(CountVarsEndingIn(built, "t", "slot"), 4u);
  EXPECT_EQ(CountVarsEndingIn(built, "t", "picked"), 1u);

  // The identical construct under the version this one is defined from, where
  // both names are still reserved and so cannot be declared.
  ElabFixture reserved;
  ElaborateWithPreprocessor(In2001("module t;\n"
                                   "  localparam incdir = 4;\n"
                                   "  genvar design;\n"
                                   "endmodule\n"),
                            reserved, "t");
  EXPECT_TRUE(reserved.has_errors);
}

// The bound from above: this version reserves no more than "1364-2001" does,
// so a word a later list introduces is not a data type here. `uwire` is the
// sharpest case, being the sole addition of the very next version. The same
// source outside the region does elaborate, which is what shows the region --
// and not some unrelated limitation -- is doing the rejecting.
TEST(NoconfigKeywordElaboration, WordOutsideTheListIsNotADataType) {
  const char* kDecls[] = {"logic [7:0] v;", "uwire v;", "bit [7:0] v;"};
  for (const char* decl : kDecls) {
    ElabFixture in_region;
    ElaborateWithPreprocessor(
        InNoconfig(std::string("module t;\n  ") + decl + "\nendmodule\n"),
        in_region, "t");
    EXPECT_TRUE(in_region.has_errors) << decl;

    ElabFixture outside;
    auto* design = ElaborateWithPreprocessor(
        std::string("module t;\n  ") + decl + "\nendmodule\n", outside, "t");
    ASSERT_NE(design, nullptr) << decl;
    EXPECT_FALSE(outside.has_errors) << decl;
  }
}

}  // namespace
