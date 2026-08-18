#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(Elaboration, StringVarIsString) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "s") {
      found = true;
      EXPECT_TRUE(v.is_string);
    }
  }
  EXPECT_TRUE(found) << "string variable 's' not found";
}

TEST(Elaboration, StringDefaultEmptyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, StringWithLiteralInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s = \"test\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.16, Table 6-9: a string replication multiplier shall be a non-negative,
// non-x, non-z integral expression. A multiplier containing x is rejected, and
// the report is the §11.4.12.1 one that governs every replication multiplier;
// it stands at the multiplier literal.
TEST(Elaboration, StringReplicationXZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = {1'bx{\"ab\"}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

// §6.16: "A single character of a string variable may be selected for reading
// or writing by indexing the variable." Both directions are accepted: the read
// and the write are the same selection.
TEST(Elaboration, StringVarMayBeIndexedForReadingAndWriting) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"world\";\n"
             "  byte c;\n"
             "  initial begin\n"
             "    c = s[2];\n"
             "    s[1] = \"a\";\n"
             "  end\n"
             "endmodule\n"));
}

// The same rule reaches a variable whose type is written as a name: what
// decides whether indexing is a character selection is the type the name
// stands for, not the spelling at the declaration.
TEST(Elaboration, IndexingAVarOfTypedefedStringType) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef string str_t;\n"
             "  str_t s = \"world\";\n"
             "  byte c;\n"
             "  initial c = s[2];\n"
             "endmodule\n"));
}

// The control the two above need. §11.5.1 leaves a bit-select of a scalar
// illegal, and a one-bit logic variable is such a scalar, so indexing one is
// still an error. Without this, an elaborator that simply stopped checking
// selects would satisfy both tests above while enforcing nothing.
TEST(Elaboration, IndexingAScalarLogicVarIsStillRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s;\n"
      "  logic c;\n"
      "  initial c = s[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

// §6.16's Table 6-9 (printed page 114) gives concatenation over string
// operands: "Each operand can be a string literal or an expression of string
// type ... the result of the concatenation shall be of string type." §11.2.1
// lists "parameters" among the operands a constant expression consists of, so
// `{P, "c"}` is one and Q holds the joined characters.
//
// The characters are read back rather than Q's resolved_value, which §11.10
// packs from the same expression and would answer whether or not §6.16 gave
// the concatenation a string result at all.
TEST(Elaboration, StringParameterConcatenationFoldsToTheJoinedCharacters) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam string P = \"ab\";\n"
      "  localparam string Q = {P, \"c\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

// The same concatenation written inside a generate block. §27.4 makes a
// generate block "a separate scope and a new level of hierarchy when it is
// instantiated", and §6.16 says nothing that would stop at that boundary, so
// the block's own P is what the concatenation names and Q holds the same three
// characters the module-level case above gives it.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamRangeRegistryGuard:
// StringParamChars in src/elaborator/const_eval.cpp answers from the
// registered module, there is none for the whole of a block's body, and the
// concatenation recovers no characters at all, leaving resolved_string empty.
TEST(Elaboration, StringParameterConcatenationFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"ab\";\n"
      "      localparam string Q = {P, \"c\"};\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

}  // namespace
