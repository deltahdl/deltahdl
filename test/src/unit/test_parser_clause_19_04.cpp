#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SourceText, ClassCovergroupDecl) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kCovergroup);
  EXPECT_EQ(members[0]->name, "cg");
}

// §19.4: a class can have more than one covergroup. Both embedded covergroups
// are recognized as distinct class members, each named by its identifier.
TEST(SourceText, MultipleCovergroupsInClass) {
  auto r = Parse(
      "class MC;\n"
      "  logic [3:0] m_x;\n"
      "  local logic m_z;\n"
      "  bit clk;\n"
      "  covergroup cv1 @(posedge clk);\n"
      "    coverpoint m_x;\n"
      "  endgroup\n"
      "  covergroup cv2 @(negedge clk);\n"
      "    coverpoint m_z;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  std::vector<std::string_view> cg_names;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kCovergroup) cg_names.push_back(m->name);
  }
  ASSERT_EQ(cg_names.size(), 2u);
  EXPECT_EQ(cg_names[0], "cv1");
  EXPECT_EQ(cg_names[1], "cv2");
}

}  // namespace
