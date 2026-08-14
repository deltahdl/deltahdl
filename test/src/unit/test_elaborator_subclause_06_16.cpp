#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

}  // namespace
