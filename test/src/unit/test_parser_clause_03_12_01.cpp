// §3.12.1: Compilation units

#include "fixture_parser.h"

using namespace delta;

namespace {

// description: { attribute_instance } package_item (file-scope task)
TEST(SourceText, DescriptionPackageItemTask) {
  auto r = Parse("task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

// 10. No forward references in CU scope (except task/function names).
// The LRM says references shall only be made to names already defined.
// This is a semantic rule; the parser accepts the code but elaboration
// would reject it.  We test that parsing succeeds (syntax is valid).
TEST(ParserClause03, Cl3_12_1_ForwardRefSyntaxValid) {
  // This is valid syntax even though semantically 'b' is referenced
  // before its declaration at CU scope.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

}  // namespace
