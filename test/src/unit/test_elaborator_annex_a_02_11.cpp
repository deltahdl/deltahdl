#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CovergroupDeclElaboration, BasicCovergroupElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithClockingEventElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithPortListElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg(ref int x, input bit [3:0] y);\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithEndLabelElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup : cg\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithCoverpointsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp1: coverpoint addr;\n"
      "    cp2: coverpoint data;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithBinsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint addr {\n"
      "      bins low = {[0:15]};\n"
      "      bins high = {[16:31]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithCrossElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    cross a, b;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithOptionsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max = 64;\n"
      "    option.weight = 2;\n"
      "    type_option.weight = 3;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupInClassElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, MultipleCovergroupsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  covergroup cg2;\n"
      "    coverpoint b;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithBlockEventElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @@(begin test_phase or end test_phase);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, CovergroupWithSampleFunctionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg with function sample(int val);\n"
      "    coverpoint val;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CovergroupDeclElaboration, FullCovergroupElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    option.auto_bin_max = 64;\n"
      "    cp_addr: coverpoint addr {\n"
      "      bins low = {[0:63]};\n"
      "      bins mid = {[64:191]};\n"
      "      bins high = {[192:255]};\n"
      "    }\n"
      "    cp_data: coverpoint data;\n"
      "    cross cp_addr, cp_data;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.2.11 gives covergroup_declaration a second alternative,
//
//   covergroup extends covergroup_identifier ;
//     { coverage_spec_or_option }
//   endgroup [ : covergroup_identifier ]
//
// which carries a footnote, and §19.4.1 is where that footnote leads: the
// alternative belongs to embedded covergroups, and "it shall be an error to use
// the extends declaration if the covergroup_identifier has not previously been
// defined in a base class of the enclosing class". A covergroup declared in a
// module has no enclosing class, so no covergroup_identifier can satisfy that
// requirement and the form is rejected wherever it appears outside one.
//
// Note the alternative names no derived covergroup of its own -- the identifier
// follows extends and names the base, and the derived covergroup takes that
// same name. The legal in-class uses live in the §19.4.1 file.
TEST(CovergroupDeclElaboration, CovergroupExtendsOutsideAClassIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  covergroup extends parent;\n"
      "    coverpoint z;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a covergroup may only use 'extends' inside a "
                            "class",
                            2, "19.3"));
}

}  // namespace
