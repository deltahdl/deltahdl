#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The additions of this version doing their elaborated job rather than merely
// lexing as keywords: `localparam` produces a resolved constant,
// `genvar`/`generate`/`endgenerate` produce one copy of the loop body per
// iteration, and `signed`/`unsigned` select what they select. They are tied
// together deliberately. The localparam is the loop bound, so the number of
// declarations reaching the design can only come out right if it resolved; and
// the nested condition picks out a single iteration, so the genvar has to hold
// a different constant on each pass rather than merely make the loop run the
// right number of times.
TEST(Verilog2001KeywordElaboration, AdditionsDoTheirElaboratedJob) {
  ExpectTable222DeclarationsElaborate("1364-2001");
}

// A declaration's width can come from any of the constant forms, and each
// reaches the elaborator by a different path. This version is the first whose
// list makes them all writable at once: the literal and the `parameter` are
// inherited, while `localparam` and the `automatic` function whose call is
// folded are both additions. Every form has to arrive at the same width. The
// remaining constant form, a genvar, is covered by the loop generate test
// above.
TEST(Verilog2001KeywordElaboration, ConstantFormsAllProduceTheSameWidth) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2001("module t;\n"
             "  parameter  P = 8;\n"
             "  localparam L = 8;\n"
             "  function automatic integer widthof(input reg [7:0] n);\n"
             "    widthof = n;\n"
             "  endfunction\n"
             "  reg [7:0]            from_literal;\n"
             "  reg [P-1:0]          from_parameter;\n"
             "  reg [L-1:0]          from_localparam;\n"
             "  reg [widthof(8)-1:0] from_function;\n"
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

// The inclusion half at this stage: the variable and net type keywords the
// earlier list names still declare their own storage under this one, each with
// the width, the real/vector distinction, and the net type its own type
// implies.
TEST(Verilog2001KeywordElaboration, InheritedTypeKeywordsKeepTheirStorage) {
  struct VarCase {
    const char* decl;
    uint32_t width;
    bool is_real;
  };
  const VarCase kVarCases[] = {
      {"reg v;", 1, false},      {"reg [15:0] v;", 16, false},
      {"integer v;", 32, false}, {"time v;", 64, false},
      {"real v;", 64, true},     {"realtime v;", 64, true},
  };
  for (const auto& c : kVarCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In2001(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* v = FindVar(design, "t", "v");
    ASSERT_NE(v, nullptr) << c.decl;
    EXPECT_EQ(v->width, c.width) << c.decl;
    EXPECT_EQ(v->is_real, c.is_real) << c.decl;
  }

  struct NetCase {
    const char* decl;
    NetType type;
  };
  const NetCase kNetCases[] = {
      {"wand n;", NetType::kWand},       {"wor n;", NetType::kWor},
      {"triand n;", NetType::kTriand},   {"trior n;", NetType::kTrior},
      {"tri0 n;", NetType::kTri0},       {"tri1 n;", NetType::kTri1},
      {"trireg n;", NetType::kTrireg},   {"supply0 n;", NetType::kSupply0},
      {"supply1 n;", NetType::kSupply1}, {"tri n;", NetType::kTri},
  };
  for (const auto& c : kNetCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In2001(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* n = FindNet(design, "t", "n");
    ASSERT_NE(n, nullptr) << c.decl;
    EXPECT_EQ(n->net_type, c.type) << c.decl;
  }
}

// Words neither table lists are ordinary identifiers under this version, and
// they stay ordinary identifiers all the way into the elaborated design: each
// names a variable that really exists there, carrying the storage its
// declaration asked for. Getting past the parser is not enough -- the design is
// what the rest of the tool works from.
TEST(Verilog2001KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ExpectFreedWordsNameElaboratedVariables("1364-2001");
}

// The elaborated design keeps nets and constants in containers of their own,
// separate from the variables above, so a freed word has to survive each of
// those paths in its own right. This also puts both sides of the rule in one
// declaration list: the constants are introduced by `parameter`, inherited from
// the earlier list, and by `localparam`, an addition of this version, while
// every name they carry is a word a later standard reserved.
TEST(Verilog2001KeywordElaboration, FreedWordsNameElaboratedNetsAndConstants) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In2001("module m;\n"
                                                  "  wire [7:0] string;\n"
                                                  "  wand       byte;\n"
                                                  "  parameter  int  = 8;\n"
                                                  "  localparam enum = 9;\n"
                                                  "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "string");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  EXPECT_EQ(n->net_type, NetType::kWire);

  n = FindNet(design, "m", "byte");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWand);

  const auto* p = FindParam(design, "m", "int");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);

  p = FindParam(design, "m", "enum");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 9);
}

// A freed word naming the design element itself, its ports, and the instance
// that binds to it -- the region governs a whole elaborated hierarchy, not one
// declaration inside one module.
TEST(Verilog2001KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ExpectFreedWordsNameModulePortsAndInstance(
      "1364-2001", {"bit", "logic", "byte", "interface"});
}

// The negative for the additions, carried to this stage: none of the words
// Table 22-2 lists can name a variable that reaches the design, while the same
// declaration under the list this version extends builds one. Sweeping all
// twenty-one rather than sampling is what makes the table, and not a handful of
// its entries, the thing being checked.
TEST(Verilog2001KeywordElaboration, AdditionsCannotNameElaboratedVariables) {
  ExpectKeywordTableIsReserved("1364-2001", kSweepTable222);
}

// The negative from the other direction: a word neither table lists carries no
// keyword meaning, so a declaration written with it as a data type does not
// elaborate. `uwire` is the sharpest case, being the sole word the very next
// version adds. The same source outside the region does elaborate, which is
// what shows the region -- and not some unrelated limitation -- is doing the
// rejecting.
TEST(Verilog2001KeywordElaboration, WordOutsideTheListIsNotADataType) {
  ExpectDeclsFailInRegionButElaborateOutside(
      "1364-2001", {"logic [7:0] v;", "uwire v;", "bit [7:0] v;"});
}

}  // namespace
