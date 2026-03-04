#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA602, ProceduralContinuous_AllForms) {

  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign q = d;\n"
      "    deassign q;\n"
      "    force y = 0;\n"
      "    release y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kDeassign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kForce);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kRelease);
}

}
