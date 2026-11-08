#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NetDeclDriveStrength, DeclaratorSharingAnAssignedStatementIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire (pull1, weak0) a = 1'b1, b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 2, "6.3.2"));
}

TEST(NetDeclDriveStrength, GenerateBlockNetWithoutAssignmentIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m #(parameter N = 1) ();\n"
      "  generate\n"
      "    if (N == 1) begin : g\n"
      "      wire (pull1, weak0) w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 4, "6.3.2"));
}

TEST(NetDeclDriveStrength, GenerateBlockNetCarryingItsAssignmentIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter N = 1) ();\n"
             "  generate\n"
             "    if (N == 1) begin : g\n"
             "      wire (pull1, weak0) w = 1'b1;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

TEST(NetDeclDriveStrength, UnselectedGenerateBranchIsNotHeldToTheRule) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter N = 1) ();\n"
             "  generate\n"
             "    if (N == 0) begin : g\n"
             "      wire (pull1, weak0) w;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

constexpr const char* kStrengthNeedsAssignment =
    "drive strength on net declaration requires an assignment";

TEST(NetDeclDriveStrength, EveryNetTypeIsHeldToTheRule) {
  for (const char* net_type : {"tri", "wand", "wor", "triand", "trior", "tri0",
                               "tri1", "uwire", "trireg"}) {
    ElabFixture f;
    ElabOk(
        std::format("module m;\n  {} (pull1, weak0) w;\nendmodule\n", net_type),
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrengthNeedsAssignment, 2,
                              "6.3.2"))
        << net_type;
    EXPECT_TRUE(ElabOk(std::format(
        "module m;\n  {} (pull1, weak0) w = 1'b1;\nendmodule\n", net_type)))
        << net_type;
  }
}

TEST(NetDeclDriveStrength, NetsNoStrengthAppliesToAreHeldToTheRule) {
  struct Net {
    const char* decl;
    const char* strength_rule;
  };
  for (const Net& n : {
           Net{"tri (pull0, pull1) [7:0] v", "applies only to scalar nets"},
           Net{"supply0 (pull0, pull1) v",
               "does not apply to supply0 or supply1 nets"},
           Net{"supply1 (pull0, pull1) v",
               "does not apply to supply0 or supply1 nets"},
       }) {
    const std::string kStrengthRule =
        std::string("drive strength on continuous assignment ") +
        n.strength_rule;
    ElabFixture bare;
    ElabOk(std::format("module m;\n  {};\nendmodule\n", n.decl), bare);
    EXPECT_TRUE(ReportedError(bare.diag.Diagnostics(), kStrengthNeedsAssignment,
                              2, "6.3.2"))
        << n.decl;
    EXPECT_TRUE(
        ReportedError(bare.diag.Diagnostics(), kStrengthRule, 2, "10.3.4"))
        << n.decl;
    ElabFixture assigned;
    ElabOk(std::format("module m;\n  {} = 1'b1;\nendmodule\n", n.decl),
           assigned);
    EXPECT_FALSE(ReportedError(assigned.diag.Diagnostics(),
                               kStrengthNeedsAssignment, 2, "6.3.2"))
        << n.decl;
    EXPECT_TRUE(
        ReportedError(assigned.diag.Diagnostics(), kStrengthRule, 2, "10.3.4"))
        << n.decl;
  }
}

TEST(NetDeclDriveStrength, EveryInstantiatedScopeIsHeldToTheRule) {
  struct Place {
    const char* before;
    const char* after;
    uint32_t line;
  };
  for (const Place& p : {
           Place{"interface i;\n",
                 "endinterface\nmodule m;\n  i u();\nendmodule\n", 2},
           Place{"program p;\n", "endprogram\nmodule m;\n  p u();\nendmodule\n",
                 2},
           Place{"module m;\n  module inner;\n",
                 "  endmodule\n  inner u();\nendmodule\n", 3},
       }) {
    ElabFixture f;
    ElabOk(std::format("{}  wire (pull1, weak0) w;\n{}", p.before, p.after), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrengthNeedsAssignment,
                              p.line, "6.3.2"))
        << p.before;
    EXPECT_TRUE(ElabOk(std::format("{}  wire (pull1, weak0) w = 1'b1;\n{}",
                                   p.before, p.after)))
        << p.before;
  }
}

TEST(NetDeclDriveStrength, CompilationUnitNetIsHeldToTheRule) {
  ElabFixture bare;
  ElabOk(
      "wire (pull1, weak0) w;\n"
      "module m;\n"
      "endmodule\n",
      bare);
  EXPECT_TRUE(ReportedError(bare.diag.Diagnostics(), kStrengthNeedsAssignment,
                            1, "6.3.2"));
  ElabFixture assigned;
  ElabOk(
      "wire (pull1, weak0) w = 1'b1;\n"
      "module m;\n"
      "endmodule\n",
      assigned);
  EXPECT_FALSE(ReportedError(assigned.diag.Diagnostics(),
                             kStrengthNeedsAssignment, 1, "6.3.2"));
  EXPECT_TRUE(ReportedError(assigned.diag.Diagnostics(),
                            "a net declaration with an implicit continuous "
                            "assignment cannot stand in the compilation-unit "
                            "scope",
                            1, "3.12.1"));
  EXPECT_TRUE(
      ElabOk("wire w;\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(NetDeclDriveStrength, PackageNetIsHeldToTheRule) {
  ElabFixture bare;
  ElabOk(
      "package p;\n"
      "  wire (pull1, weak0) w;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      bare);
  EXPECT_TRUE(ReportedError(bare.diag.Diagnostics(), kStrengthNeedsAssignment,
                            2, "6.3.2"));
  ElabFixture assigned;
  ElabOk(
      "package p;\n"
      "  wire (pull1, weak0) w = 1'b1;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      assigned);
  EXPECT_FALSE(ReportedError(assigned.diag.Diagnostics(),
                             kStrengthNeedsAssignment, 2, "6.3.2"));
  EXPECT_TRUE(ReportedError(assigned.diag.Diagnostics(),
                            "net declaration with implicit continuous "
                            "assignment is not allowed in a package",
                            2, "26.2"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  wire w;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
