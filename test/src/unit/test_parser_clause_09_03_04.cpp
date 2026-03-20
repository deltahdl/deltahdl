#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleAndHierarchyParsing, EndLabelInterface) {
  auto r = Parse("interface myif; endinterface : myif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(ModuleAndHierarchyParsing, EndLabelProgram) {
  auto r = Parse("program myprog; endprogram : myprog\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "myprog");
}

// §3.1 — Error: mismatched end label.
TEST(BlockNames, MismatchedEndLabelIsError) {
  EXPECT_FALSE(ParseOk("module foo; endmodule : bar\n"));
}

}  // namespace
